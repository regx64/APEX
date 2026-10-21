//! A lazy (call-by-need) environment machine for the erased IR.
//!
//! Laziness matters here: definitions are compiled to recursors, and a
//! recursor's induction hypotheses must not be computed unless the branch
//! uses them. `Nat` is a machine integer; `Nat.add`/`Nat.mul` are intrinsics.

use crate::erase::{Eraser, Ir};
use apex_kernel::{Decl, Env};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

type R<X> = Result<X, String>;

pub struct Node {
    val: Value,
    next: EnvList,
}
pub type EnvList = Option<Rc<Node>>;

fn cons(v: Value, env: &EnvList) -> EnvList {
    Some(Rc::new(Node {
        val: v,
        next: env.clone(),
    }))
}

fn lookup(env: &EnvList, mut i: usize) -> R<Value> {
    let mut cur = env;
    loop {
        match cur {
            None => return Err("internal error: unbound runtime variable".into()),
            Some(n) if i == 0 => return Ok(n.val.clone()),
            Some(n) => {
                i -= 1;
                cur = &n.next;
            }
        }
    }
}

pub enum Th {
    Pending(Rc<Ir>, EnvList),
    Done(Value),
    Running,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Ctor,
    Rec,
    NatSucc,
    NatAdd,
    NatMul,
    /// String and IO primitives, dispatched by name.
    Prim,
}

pub struct FunInfo {
    kind: Kind,
    name: Rc<str>,
    arity: usize,
}

#[derive(Clone)]
pub enum Value {
    Nat(u128),
    Str(Rc<str>),
    /// An `IO` action; running it performs the effects.
    Io(Rc<IoAct>),
    Ctor(Rc<str>, Rc<Vec<Value>>),
    Closure(Rc<Ir>, EnvList),
    Fun(Rc<FunInfo>, Rc<Vec<Value>>),
    Erased,
    Thunk(Rc<RefCell<Th>>),
}

pub enum IoAct {
    Pure(Value),
    Bind(Value, Value),
    Print(Value),
}

pub struct Evaluator<'a> {
    env: &'a Env,
    out: RefCell<String>,
    globals: RefCell<HashMap<String, Value>>,
    rules: RefCell<HashMap<String, Value>>,
}

impl<'a> Evaluator<'a> {
    pub fn new(env: &'a Env) -> Self {
        Evaluator {
            env,
            out: RefCell::default(),
            globals: RefCell::default(),
            rules: RefCell::default(),
        }
    }

    pub fn force(&self, v: &Value) -> R<Value> {
        let Value::Thunk(t) = v else {
            return Ok(v.clone());
        };
        let state = std::mem::replace(&mut *t.borrow_mut(), Th::Running);
        match state {
            Th::Done(v) => {
                *t.borrow_mut() = Th::Done(v.clone());
                Ok(v)
            }
            Th::Pending(ir, env) => {
                let r = self.eval(&ir, &env)?;
                *t.borrow_mut() = Th::Done(r.clone());
                Ok(r)
            }
            Th::Running => Err("infinite loop: a value depends on itself".into()),
        }
    }

    fn delay(&self, ir: &Rc<Ir>, env: &EnvList) -> R<Value> {
        Ok(match &**ir {
            Ir::Erased => Value::Erased,
            Ir::Nat(n) => Value::Nat(*n),
            Ir::Str(t) => Value::Str(t.clone()),
            Ir::Var(i) => lookup(env, *i)?,
            Ir::Lam(b) => Value::Closure(b.clone(), env.clone()),
            _ => Value::Thunk(Rc::new(RefCell::new(Th::Pending(ir.clone(), env.clone())))),
        })
    }

    pub fn eval(&self, ir: &Rc<Ir>, env: &EnvList) -> R<Value> {
        match &**ir {
            Ir::Var(i) => self.force(&lookup(env, *i)?),
            Ir::Lam(b) => Ok(Value::Closure(b.clone(), env.clone())),
            Ir::App(f, a) => {
                let fv = self.eval(f, env)?;
                let av = self.delay(a, env)?;
                self.apply(fv, av)
            }
            Ir::Global(n) => self.global(n),
            Ir::Erased => Ok(Value::Erased),
            Ir::Nat(n) => Ok(Value::Nat(*n)),
            Ir::Str(t) => Ok(Value::Str(t.clone())),
            Ir::Let(v, b) => {
                let vv = self.delay(v, env)?;
                self.eval(b, &cons(vv, env))
            }
        }
    }

    fn apply(&self, f: Value, a: Value) -> R<Value> {
        match self.force(&f)? {
            Value::Closure(b, cenv) => self.eval(&b, &cons(a, &cenv)),
            Value::Fun(info, args) => {
                let mut v = (*args).clone();
                v.push(a);
                if v.len() == info.arity {
                    self.exec(&info, v)
                } else {
                    Ok(Value::Fun(info, Rc::new(v)))
                }
            }
            Value::Erased => Ok(Value::Erased),
            _ => Err("internal error: applying a value that is not a function".into()),
        }
    }

    fn force_nat(&self, v: &Value) -> R<u128> {
        match self.force(v)? {
            Value::Nat(n) => Ok(n),
            _ => Err("internal error: expected a natural number".into()),
        }
    }

    fn force_str(&self, v: &Value) -> R<Rc<str>> {
        match self.force(v)? {
            Value::Str(s) => Ok(s),
            _ => Err("internal error: expected a string".into()),
        }
    }

    /// Run an `IO` action to completion, appending its output to the buffer.
    /// Continuations live on an explicit stack so long `do` chains and loops
    /// do not grow the Rust stack.
    pub fn run_io(&self, action: Value) -> R<Value> {
        let mut conts: Vec<Value> = Vec::new();
        let mut cur = self.force(&action)?;
        loop {
            let Value::Io(act) = &cur else {
                return Err("internal error: expected an IO action".into());
            };
            let result = match &**act {
                IoAct::Bind(m, k) => {
                    conts.push(k.clone());
                    cur = self.force(m)?;
                    continue;
                }
                IoAct::Pure(v) => v.clone(),
                IoAct::Print(s) => {
                    let text = self.force_str(s)?;
                    self.out.borrow_mut().push_str(&text);
                    Value::Ctor("Unit.unit".into(), Rc::new(vec![]))
                }
            };
            match conts.pop() {
                None => return Ok(result),
                Some(k) => {
                    let next = self.apply(k, result)?;
                    cur = self.force(&next)?;
                }
            }
        }
    }

    pub fn take_output(&self) -> String {
        std::mem::take(&mut *self.out.borrow_mut())
    }

    fn exec(&self, info: &FunInfo, args: Vec<Value>) -> R<Value> {
        match info.kind {
            Kind::Ctor => Ok(Value::Ctor(info.name.clone(), Rc::new(args))),
            Kind::NatSucc => {
                let n = self.force_nat(&args[0])?;
                n.checked_add(1)
                    .map(Value::Nat)
                    .ok_or_else(|| "Nat overflow".to_string())
            }
            Kind::NatAdd => {
                let (a, b) = (self.force_nat(&args[0])?, self.force_nat(&args[1])?);
                a.checked_add(b)
                    .map(Value::Nat)
                    .ok_or_else(|| "Nat overflow".to_string())
            }
            Kind::NatMul => {
                let (a, b) = (self.force_nat(&args[0])?, self.force_nat(&args[1])?);
                a.checked_mul(b)
                    .map(Value::Nat)
                    .ok_or_else(|| "Nat overflow".to_string())
            }
            Kind::Rec => self.exec_rec(&info.name, args),
            Kind::Prim => match &*info.name {
                "String.append" => {
                    let (a, b) = (self.force_str(&args[0])?, self.force_str(&args[1])?);
                    Ok(Value::Str(format!("{a}{b}").into()))
                }
                "nat_sub" => {
                    let (a, b) = (self.force_nat(&args[0])?, self.force_nat(&args[1])?);
                    Ok(Value::Nat(a.saturating_sub(b)))
                }
                "nat_beq" | "nat_lt" => {
                    let (a, b) = (self.force_nat(&args[0])?, self.force_nat(&args[1])?);
                    let r = if &*info.name == "nat_beq" {
                        a == b
                    } else {
                        a < b
                    };
                    let name = if r { "Bool.true" } else { "Bool.false" };
                    Ok(Value::Ctor(name.into(), Rc::new(vec![])))
                }
                "Nat.toString" => Ok(Value::Str(self.force_nat(&args[0])?.to_string().into())),
                // IO.pure α x / IO.bind α β m k / IO.print s
                "IO.pure" => Ok(Value::Io(Rc::new(IoAct::Pure(args[1].clone())))),
                "IO.bind" => Ok(Value::Io(Rc::new(IoAct::Bind(
                    args[2].clone(),
                    args[3].clone(),
                )))),
                "IO.print" => Ok(Value::Io(Rc::new(IoAct::Print(args[0].clone())))),
                other => Err(format!("internal error: unknown primitive `{other}`")),
            },
        }
    }

    fn exec_rec(&self, rec_name: &str, args: Vec<Value>) -> R<Value> {
        let Some(Decl::Rec(r)) = self.env.get(rec_name) else {
            return Err(format!("internal error: `{rec_name}` is not a recursor"));
        };
        let major_idx = r.nparams + 1 + r.nminors + r.nindices;
        let major = self.force(&args[major_idx])?;
        let (rule, fields): (_, Vec<Value>) = match major {
            Value::Nat(n) => {
                let (c, fs) = if n == 0 {
                    ("Nat.zero", vec![])
                } else {
                    ("Nat.succ", vec![Value::Nat(n - 1)])
                };
                (r.rules.iter().find(|ru| &*ru.ctor == c), fs)
            }
            Value::Ctor(c, cargs) => {
                let rule = r.rules.iter().find(|ru| ru.ctor == c);
                let nparams = match self.env.get(&c) {
                    Some(Decl::Ctor(ci)) => ci.nparams,
                    _ => return Err(format!("internal error: `{c}` is not a constructor")),
                };
                (rule, cargs[nparams..].to_vec())
            }
            // a proof (erased): only a subsingleton eliminator can run
            Value::Erased if r.rules.len() == 1 => {
                (r.rules.first(), vec![Value::Erased; r.rules[0].nfields])
            }
            _ => {
                return Err(format!(
                    "internal error: cannot eliminate this value with `{rec_name}`"
                ))
            }
        };
        let Some(rule) = rule else {
            return Err(format!(
                "internal error: no rule of `{rec_name}` for this constructor"
            ));
        };
        let rv = {
            let cached = self.rules.borrow().get(&*rule.ctor).cloned();
            match cached {
                Some(v) => v,
                None => {
                    let ir = Eraser::new(self.env).erase_closed(&rule.rhs)?;
                    let v = self.eval(&ir, &None)?;
                    self.rules
                        .borrow_mut()
                        .insert(rule.ctor.to_string(), v.clone());
                    v
                }
            }
        };
        let mut cur = rv;
        for a in &args[..r.nparams + 1 + r.nminors] {
            cur = self.apply(cur, a.clone())?;
        }
        for f in fields {
            cur = self.apply(cur, f)?;
        }
        for a in &args[major_idx + 1..] {
            cur = self.apply(cur, a.clone())?;
        }
        self.force(&cur)
    }

    pub fn global(&self, name: &str) -> R<Value> {
        if let Some(v) = self.globals.borrow().get(name) {
            return Ok(v.clone());
        }
        let fun = |kind, arity| {
            Value::Fun(
                Rc::new(FunInfo {
                    kind,
                    name: name.into(),
                    arity,
                }),
                Rc::new(vec![]),
            )
        };
        let v = match name {
            "Nat.zero" => Value::Nat(0),
            "Nat.succ" => fun(Kind::NatSucc, 1),
            "Nat.add" => fun(Kind::NatAdd, 2),
            "Nat.mul" => fun(Kind::NatMul, 2),
            // native versions of prelude definitions (same behavior, faster)
            "nat_sub" | "nat_beq" | "nat_lt" => fun(Kind::Prim, 2),
            "String.append" => fun(Kind::Prim, 2),
            "Nat.toString" => fun(Kind::Prim, 1),
            "IO.pure" => fun(Kind::Prim, 2),
            "IO.bind" => fun(Kind::Prim, 4),
            "IO.print" => fun(Kind::Prim, 1),
            _ => match self.env.get(name) {
                Some(Decl::Def { val, .. }) => {
                    let ir = Eraser::new(self.env).erase_closed(val)?;
                    self.eval(&ir, &None)?
                }
                Some(Decl::Ctor(ci)) => {
                    let arity = ci.nparams + ci.nfields;
                    if arity == 0 {
                        Value::Ctor(name.into(), Rc::new(vec![]))
                    } else {
                        fun(Kind::Ctor, arity)
                    }
                }
                Some(Decl::Rec(r)) => fun(Kind::Rec, r.nparams + 1 + r.nminors + r.nindices + 1),
                Some(Decl::Inductive(_)) => Value::Erased,
                Some(Decl::Axiom { .. }) => {
                    return Err(format!("the axiom `{name}` has no runtime value"))
                }
                None => return Err(format!("unknown constant `{name}`")),
            },
        };
        self.globals
            .borrow_mut()
            .insert(name.to_string(), v.clone());
        Ok(v)
    }

    /// Fully evaluate and render a value.
    pub fn show(&self, v: &Value) -> R<String> {
        match self.force(v)? {
            Value::Nat(n) => Ok(n.to_string()),
            Value::Erased => Ok("_".into()),
            Value::Str(t) => Ok(format!("{t:?}")),
            Value::Io(_) => Ok("<io action>".into()),
            Value::Closure(..) | Value::Fun(..) => Ok("<function>".into()),
            Value::Thunk(_) => unreachable!("force returns a value"),
            Value::Ctor(name, args) => {
                match &*name {
                    "Unit.unit" => return Ok("()".into()),
                    "Bool.true" => return Ok("true".into()),
                    "Bool.false" => return Ok("false".into()),
                    _ => {}
                }
                let nparams = match self.env.get(&name) {
                    Some(Decl::Ctor(ci)) => ci.nparams,
                    _ => 0,
                };
                let mut parts_of_name = name.rsplit('.');
                let last = parts_of_name.next().unwrap_or(&name);
                let short = match (last, parts_of_name.next()) {
                    ("mk", Some(ty)) => ty.to_string(),
                    _ => last.to_string(),
                };
                let mut parts = Vec::new();
                for a in &args[nparams..] {
                    if !matches!(self.force(a)?, Value::Erased) {
                        parts.push(self.show(a)?);
                    }
                }
                Ok(if parts.is_empty() {
                    short
                } else {
                    format!("{short}({})", parts.join(", "))
                })
            }
        }
    }
}
