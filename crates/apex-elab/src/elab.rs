//! Bidirectional elaboration with metavariables and implicit arguments.

use apex_kernel::prelude::add_prelude;
use apex_kernel::term::*;
use apex_kernel::{Decl, Env, InductiveDecl, KResult, KernelError, Level, Mult, TypeChecker};
use apex_span::Span;
use apex_syntax::ast::*;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElabError {
    pub msg: String,
    pub span: Span,
}

type R<X> = Result<X, ElabError>;

fn err<X>(span: Span, msg: impl Into<String>) -> R<X> {
    Err(ElabError {
        msg: msg.into(),
        span,
    })
}

fn from_kernel<X>(r: KResult<X>, span: Span) -> R<X> {
    r.map_err(|KernelError(msg)| ElabError { msg, span })
}

/// An argument to an application: surface syntax, or an already elaborated term.
enum Arg<'e> {
    Expr(&'e Expr),
    Term(T),
}

enum Res {
    Local(T),
    Global(String),
}

/// Which binders of a constant's type are implicit.
type Masks = HashMap<String, Vec<bool>>;
type Aliases = HashMap<String, String>;

pub struct Elaborator {
    env: Env,
    masks: Masks,
    aliases: Aliases,
}

impl Default for Elaborator {
    fn default() -> Self {
        Self::new()
    }
}

impl Elaborator {
    /// An elaborator with the kernel prelude and `prelude.apex` loaded.
    pub fn new() -> Elaborator {
        let mut env = Env::new();
        add_prelude(&mut env).expect("kernel prelude must check");
        let mut masks = Masks::new();
        masks.insert("Eq".into(), vec![true, false, false]);
        masks.insert("Eq.refl".into(), vec![true, false]);
        masks.insert("IO.pure".into(), vec![true, false]);
        masks.insert("IO.bind".into(), vec![true, true, false, false]);
        let mut aliases = Aliases::new();
        aliases.insert("true".into(), "Bool.true".into());
        aliases.insert("false".into(), "Bool.false".into());
        aliases.insert("print".into(), "IO.print".into());
        aliases.insert("pure".into(), "IO.pure".into());
        let mut el = Elaborator {
            env,
            masks,
            aliases,
        };
        let module = apex_syntax::parse(include_str!("prelude.apex")).expect("prelude must parse");
        el.elab_module(&module)
            .unwrap_or_else(|e| panic!("prelude must elaborate: {}", e.msg));
        el
    }

    pub fn env(&self) -> &Env {
        &self.env
    }

    pub fn elab_module(&mut self, m: &Module) -> R<()> {
        for item in &m.items {
            self.elab_item(item)?;
        }
        Ok(())
    }

    fn elab_item(&mut self, item: &Item) -> R<()> {
        match &item.kind {
            ItemKind::Fn(f) => self.elab_fn(f, item.span),
            ItemKind::Theorem(t) => self.elab_theorem(t, item.span),
            ItemKind::Enum(e) => self.elab_enum(e, item.span),
            ItemKind::Struct(s) => self.elab_struct(s, item.span),
            ItemKind::Trait(_) | ItemKind::Impl(_) => err(
                item.span,
                "traits and impls are not supported by the elaborator yet (M3b)",
            ),
        }
    }

    fn cx(&self) -> Cx<'_> {
        Cx::new(&self.env, &self.masks, &self.aliases)
    }

    fn add_def(&mut self, name: &Ident, ty: T, val: T, mask: Vec<bool>) -> R<()> {
        from_kernel(self.env.add_def(&name.name, &[], ty, val), name.span)?;
        self.masks.insert(name.name.clone(), mask);
        Ok(())
    }

    fn elab_fn(&mut self, f: &FnDecl, span: Span) -> R<()> {
        let recursive = f
            .body
            .as_ref()
            .is_some_and(|b| mentions_block(b, &f.name.name));
        let (ty, val, mask) = if !recursive {
            self.try_fn(f, span, None)?
        } else {
            // structural recursion: try each parameter as the decreasing one
            let mut first_err = None;
            let mut found = None;
            for k in 0..f.params.len() {
                match self.try_fn(f, span, Some(k)) {
                    Ok(r) => {
                        found = Some(r);
                        break;
                    }
                    Err(e) => {
                        first_err.get_or_insert(e);
                    }
                }
            }
            match found {
                Some(r) => r,
                None => {
                    return Err(first_err.unwrap_or(ElabError {
                        msg: "a recursive function needs at least one parameter to recurse on"
                            .into(),
                        span: f.name.span,
                    }))
                }
            }
        };
        self.add_def(&f.name, ty, val, mask)
    }

    /// Elaborate a function; `decr` is the index (among `params`) of the
    /// parameter a recursive function decreases on.
    fn try_fn(&self, f: &FnDecl, span: Span, decr: Option<usize>) -> R<(T, T, Vec<bool>)> {
        let mut cx = self.cx();
        let (fvs, mask) = cx.elab_binders(&f.generics, &f.params)?;
        if let Some(k) = decr {
            let nparams = f.params.len();
            let explicit: Vec<u32> = fvs[fvs.len() - nparams..].to_vec();
            let d = explicit[k];
            let dty = from_kernel(cx.tc.local_ty(d), span)?;
            let dty = from_kernel(cx.tc.whnf(&dty), span)?;
            let (h, _) = app_spine(&dty);
            let inductive = matches!(&*h, Term::Const(n, _) if matches!(self.env.get(n), Some(Decl::Inductive(_))));
            if !inductive {
                return err(
                    f.params[k].name.span,
                    "cannot recurse on a parameter whose type is not an inductive type",
                );
            }
            cx.rec = Some(RecCtx {
                name: f.name.name.clone(),
                decr: d,
                explicit,
                fields: HashMap::new(),
                in_top: false,
            });
        }
        let ret = match &f.ret {
            Some(t) => cx.elab_type(t)?,
            None => cx.unit_type(),
        };
        let Some(block) = &f.body else {
            return err(f.name.span, "a function needs a body");
        };
        let body = cx.elab_block(block, Some(&ret))?;
        let body = cx.coerce(body, &ret, block.span)?;
        Ok((
            cx.close(&fvs, &ret, true, span)?,
            cx.close(&fvs, &body, false, span)?,
            mask,
        ))
    }

    fn elab_theorem(&mut self, t: &TheoremDecl, span: Span) -> R<()> {
        let (ty, val, mask) = {
            let mut cx = self.cx();
            let (fvs, mask) = cx.elab_binders(&t.generics, &t.params)?;
            let stmt = cx.elab_type(&t.stmt)?;
            let proof = match &t.proof {
                Proof::Term(e) => cx.elab_check(e, &stmt)?,
                Proof::Tactic(_) => return err(span, "tactic proofs are not implemented yet (M6)"),
            };
            (
                cx.close(&fvs, &stmt, true, span)?,
                cx.close(&fvs, &proof, false, span)?,
                mask,
            )
        };
        self.add_def(&t.name, ty, val, mask)
    }

    /// Elaborate the inductive type former's type: `Π params, Type`.
    fn ind_type(&self, generics: &[Generic], span: Span) -> R<T> {
        let mut cx = self.cx();
        let (pfv, _) = cx.elab_binders(generics, &[])?;
        cx.close(&pfv, &sort(Level::of_nat(1)), true, span)
    }

    fn register_inductive(&mut self, decl: InductiveDecl, nparams: usize, span: Span) -> R<()> {
        let name = decl.name.to_string();
        let ctor_names: Vec<String> = decl.ctors.iter().map(|(n, _)| n.to_string()).collect();
        from_kernel(self.env.add_inductive(decl), span)?;
        for cn in ctor_names {
            // parameters are implicit in constructors
            self.masks.insert(cn.clone(), vec![true; nparams]);
            if let Some(short) = cn.strip_prefix(&format!("{name}.")) {
                if self.env.get(short).is_none() && !self.aliases.contains_key(short) {
                    self.aliases.insert(short.to_string(), cn.clone());
                }
            }
        }
        Ok(())
    }

    fn elab_enum(&mut self, d: &EnumDecl, span: Span) -> R<()> {
        let ind_ty = self.ind_type(&d.generics, span)?;
        let name = d.name.name.clone();
        // scratch environment in which the type is visible, for recursive fields
        let mut scratch = self.env.clone();
        from_kernel(scratch.add_axiom(&name, &[], ind_ty.clone()), d.name.span)?;
        let mut ctors = Vec::new();
        {
            let mut cx = Cx::new(&scratch, &self.masks, &self.aliases);
            for v in &d.variants {
                let (pfv, _) = cx.elab_binders(&d.generics, &[])?;
                let mut fields = Vec::new();
                for ft in &v.fields {
                    let ty = cx.elab_type(ft)?;
                    fields.push(cx.tc.fresh("_", ty, Mult::Omega));
                }
                let pargs: Vec<T> = pfv.iter().map(|&i| fvar(i)).collect();
                let result = mk_apps(&cnst(name.as_str().into(), vec![]), &pargs);
                let all: Vec<u32> = pfv.iter().chain(&fields).copied().collect();
                let cty = cx.close(&all, &result, true, v.name.span)?;
                ctors.push((format!("{name}.{}", v.name.name).as_str().into(), cty));
                cx.scope.clear();
            }
        }
        let nparams = d
            .generics
            .iter()
            .filter(|g| !g.name.name.starts_with('\''))
            .count();
        self.register_inductive(
            InductiveDecl {
                name: name.as_str().into(),
                lparams: vec![],
                nparams,
                ty: ind_ty,
                ctors,
            },
            nparams,
            span,
        )
    }

    fn elab_struct(&mut self, d: &StructDecl, span: Span) -> R<()> {
        let ind_ty = self.ind_type(&d.generics, span)?;
        let name = d.name.name.clone();
        let nparams = d
            .generics
            .iter()
            .filter(|g| !g.name.name.starts_with('\''))
            .count();
        let ctor_name = format!("{name}.mk");
        let mut scratch = self.env.clone();
        from_kernel(scratch.add_axiom(&name, &[], ind_ty.clone()), d.name.span)?;
        let ctor_ty = {
            let mut cx = Cx::new(&scratch, &self.masks, &self.aliases);
            let tele = cx.struct_telescope(d)?;
            let result = mk_apps(&cnst(name.as_str().into(), vec![]), &tele.pargs());
            let all: Vec<u32> = tele.params.iter().chain(&tele.fields).copied().collect();
            cx.close(&all, &result, true, span)?
        };
        self.register_inductive(
            InductiveDecl {
                name: name.as_str().into(),
                lparams: vec![],
                nparams,
                ty: ind_ty,
                ctors: vec![(ctor_name.as_str().into(), ctor_ty)],
            },
            nparams,
            span,
        )?;
        // projections: S.f := fun params (self : S params) => S.rec (fun _ => T_f) (fun fields => f) self
        for (j, field) in d.fields.iter().enumerate() {
            let (ty, val) = {
                let mut cx = self.cx();
                let tele = cx.struct_telescope(d)?;
                let fty = tele.field_tys[j].clone();
                if tele.fields[..j].iter().any(|&f| contains_fvar(&fty, f)) {
                    return err(
                        field.name.span,
                        "struct fields that depend on earlier fields are not supported yet",
                    );
                }
                let self_ty = mk_apps(&cnst(name.as_str().into(), vec![]), &tele.pargs());
                let s = cx.tc.fresh("self", self_ty.clone(), Mult::Omega);
                let lvl = from_kernel(cx.tc.check_is_type(&fty), field.name.span)?;
                let t0 = cx.tc.fresh("t", self_ty, Mult::Omega);
                let motive = cx.tc.mk_lam(&[t0], &fty);
                let minor = cx.tc.mk_lam(&tele.fields, &fvar(tele.fields[j]));
                let rec = cnst(format!("{name}.rec").as_str().into(), vec![lvl]);
                let mut args = tele.pargs();
                args.extend([motive, minor, fvar(s)]);
                let body = mk_apps(&rec, &args);
                let binders: Vec<u32> = tele.params.iter().copied().chain([s]).collect();
                (
                    cx.close(&binders, &fty, true, field.name.span)?,
                    cx.close(&binders, &body, false, field.name.span)?,
                )
            };
            let pname = Ident {
                name: format!("{name}.{}", field.name.name),
                span: field.name.span,
            };
            let mut mask = vec![true; nparams];
            mask.push(false);
            self.add_def(&pname, ty, val, mask)?;
        }
        Ok(())
    }
}

#[derive(Clone)]
enum Pat {
    Wild,
    Var(String),
    Ctor(String, Vec<Pat>),
}

struct Row<'e> {
    pats: Vec<Pat>,
    binds: Vec<(String, T)>,
    body: &'e Expr,
}

/// State for elaborating a structurally recursive function.
struct RecCtx {
    name: String,
    /// The decreasing parameter.
    decr: u32,
    /// All explicit parameters, in order.
    explicit: Vec<u32>,
    /// Recursive fields of the top-level match on `decr`, with their induction hypotheses.
    fields: HashMap<u32, T>,
    in_top: bool,
}

struct StructTele {
    params: Vec<u32>,
    fields: Vec<u32>,
    field_tys: Vec<T>,
}

impl StructTele {
    fn pargs(&self) -> Vec<T> {
        self.params.iter().map(|&i| fvar(i)).collect()
    }
}

/// Per-declaration elaboration context.
struct Cx<'a> {
    tc: TypeChecker<'a>,
    env: &'a Env,
    masks: &'a Masks,
    aliases: &'a Aliases,
    scope: Vec<(String, T)>,
    rec: Option<RecCtx>,
    /// Where each metavariable was created, for "cannot infer" errors.
    spans: HashMap<u32, Span>,
}

fn path_name(e: &Expr) -> Option<String> {
    match &e.kind {
        ExprKind::Var(n) => Some(n.clone()),
        ExprKind::Field(b, f) => path_name(b).map(|p| format!("{p}.{}", f.name)),
        _ => None,
    }
}

impl<'a> Cx<'a> {
    fn new(env: &'a Env, masks: &'a Masks, aliases: &'a Aliases) -> Self {
        Cx {
            tc: TypeChecker::new(env),
            env,
            masks,
            aliases,
            scope: Vec::new(),
            rec: None,
            spans: HashMap::new(),
        }
    }

    fn unit_type(&self) -> T {
        cnst("Unit".into(), vec![])
    }

    fn unit_value(&self) -> T {
        cnst("Unit.unit".into(), vec![])
    }

    fn new_mvar(&mut self, ty: T, span: Span) -> T {
        let m = self.tc.new_mvar(ty);
        if let Term::MVar(id) = &*m {
            self.spans.insert(*id, span);
        }
        m
    }

    fn pp(&self, t: &T) -> String {
        self.tc.pp(&self.tc.zonk(t))
    }

    // ---- binders ----

    fn is_sort(&mut self, ty: &T) -> bool {
        matches!(self.tc.whnf(ty).as_deref(), Ok(Term::Sort(_)))
    }

    /// Introduce generics (implicit, erased when they are types) and parameters.
    fn elab_binders(&mut self, generics: &[Generic], params: &[Param]) -> R<(Vec<u32>, Vec<bool>)> {
        let mut fvs = Vec::new();
        let mut mask = Vec::new();
        for g in generics {
            if g.name.name.starts_with('\'') {
                continue; // lifetimes are handled by the borrow checker
            }
            let ty = match &g.ty {
                Some(t) => self.elab_type(t)?,
                None => sort(Level::of_nat(1)),
            };
            let mult = if self.is_sort(&ty) {
                Mult::Zero
            } else {
                Mult::Omega
            };
            let id = self.tc.fresh(&g.name.name, ty, mult);
            self.scope.push((g.name.name.clone(), fvar(id)));
            fvs.push(id);
            mask.push(true);
        }
        for p in params {
            let ty = self.elab_type(&p.ty)?;
            let mult = match p.mode {
                Mode::Own => Mult::One,
                Mode::Default if self.is_sort(&ty) => Mult::Zero,
                Mode::Default => Mult::Omega,
            };
            let id = self.tc.fresh(&p.name.name, ty, mult);
            self.scope.push((p.name.name.clone(), fvar(id)));
            fvs.push(id);
            mask.push(false);
        }
        Ok((fvs, mask))
    }

    fn struct_telescope(&mut self, d: &StructDecl) -> R<StructTele> {
        let (params, _) = self.elab_binders(&d.generics, &[])?;
        let mut fields = Vec::new();
        let mut field_tys = Vec::new();
        for f in &d.fields {
            let ty = self.elab_type(&f.ty)?;
            let id = self.tc.fresh(&f.name.name, ty.clone(), Mult::Omega);
            self.scope.push((f.name.name.clone(), fvar(id)));
            fields.push(id);
            field_tys.push(ty);
        }
        Ok(StructTele {
            params,
            fields,
            field_tys,
        })
    }

    /// Zonk and abstract `fvs` over `body`; fails if metavariables remain.
    fn close(&mut self, fvs: &[u32], body: &T, is_pi: bool, span: Span) -> R<T> {
        self.tc.zonk_locals();
        let body = self.tc.zonk(body);
        let t = self.tc.mk_binding(fvs, &body, is_pi);
        if let Some(m) = first_mvar(&t) {
            let at = self.spans.get(&m).copied().unwrap_or(span);
            return err(
                at,
                "cannot infer this placeholder or implicit argument; add a type annotation",
            );
        }
        if has_level_mvar(&t) {
            return err(span, "cannot infer a universe level; add a type annotation");
        }
        Ok(t)
    }

    // ---- name resolution ----

    fn resolve(&self, name: &str) -> Option<Res> {
        if let Some((_, t)) = self.scope.iter().rev().find(|(n, _)| n == name) {
            return Some(Res::Local(t.clone()));
        }
        if self.env.get(name).is_some() {
            return Some(Res::Global(name.to_string()));
        }
        self.aliases.get(name).map(|full| Res::Global(full.clone()))
    }

    /// A constant applied to fresh universe level metavariables.
    fn const_term(&mut self, name: &str) -> (T, Vec<bool>) {
        let n = match self.env.get(name) {
            Some(d) => d.lparams().len(),
            None => 0,
        };
        let levels = (0..n).map(|_| self.tc.new_level_mvar()).collect();
        (
            cnst(name.into(), levels),
            self.masks.get(name).cloned().unwrap_or_default(),
        )
    }

    fn head_of(&mut self, path: &str) -> Option<(T, Vec<bool>)> {
        match path {
            "Type" => return Some((sort(Level::of_nat(1)), vec![])),
            "Prop" => return Some((sort(Level::zero()), vec![])),
            _ => {}
        }
        match self.resolve(path)? {
            Res::Local(t) => Some((t, vec![])),
            Res::Global(n) => Some(self.const_term(&n)),
        }
    }

    // ---- expressions ----

    fn elab_type(&mut self, e: &Expr) -> R<T> {
        let t = self.elab(e, None)?;
        let ty = from_kernel(self.tc.infer(&t), e.span)?;
        match from_kernel(self.tc.ensure_sort(&ty), e.span) {
            Ok(_) => Ok(t),
            Err(_) => err(e.span, format!("expected a type, found `{}`", self.pp(&t))),
        }
    }

    fn elab_check(&mut self, e: &Expr, expected: &T) -> R<T> {
        let t = self.elab(e, Some(expected))?;
        self.coerce(t, expected, e.span)
    }

    /// Check that `t` has type `expected`.
    fn coerce(&mut self, t: T, expected: &T, span: Span) -> R<T> {
        let ty = from_kernel(self.tc.infer(&t), span)?;
        if from_kernel(self.tc.is_def_eq(&ty, expected), span)? {
            Ok(t)
        } else {
            err(
                span,
                format!(
                    "type mismatch: expected `{}`, found `{}`",
                    self.pp(expected),
                    self.pp(&ty)
                ),
            )
        }
    }

    fn nat_literal(&self, n: u64, _span: Span) -> R<T> {
        Ok(lit(n))
    }

    fn elab(&mut self, e: &Expr, exp: Option<&T>) -> R<T> {
        match &e.kind {
            ExprKind::Var(_) | ExprKind::Field(..) => {
                if let Some(path) = path_name(e) {
                    if self.rec.as_ref().is_some_and(|r| r.name == path) {
                        return err(
                            e.span,
                            "a recursive function must be called with all of its arguments",
                        );
                    }
                    if let Some(head) = self.head_of(&path) {
                        return self.elab_app(head, vec![], exp, e.span);
                    }
                }
                match &e.kind {
                    ExprKind::Field(base, f) => self.elab_field(base, f, exp, e.span),
                    ExprKind::Var(n) => err(e.span, format!("unknown identifier `{n}`")),
                    _ => unreachable!(),
                }
            }
            ExprKind::Nat(n) => self.nat_literal(*n, e.span),
            ExprKind::Unit => Ok(self.unit_value()),
            ExprKind::Wild => {
                let ty = match exp {
                    Some(t) => t.clone(),
                    None => {
                        let l = self.tc.new_level_mvar();
                        self.new_mvar(sort(l), e.span)
                    }
                };
                Ok(self.new_mvar(ty, e.span))
            }
            ExprKind::Binary(op, l, r) => {
                let name = match op {
                    BinOp::Add => "Nat.add",
                    BinOp::Mul => "Nat.mul",
                    BinOp::Eq => "Eq",
                    _ => return err(e.span, "this operator is not supported yet (needs traits)"),
                };
                let head = self.const_term(name);
                self.elab_app(head, vec![Arg::Expr(l), Arg::Expr(r)], exp, e.span)
            }
            ExprKind::Arrow(a, b) => {
                let a = self.elab_type(a)?;
                let b = self.elab_type(b)?;
                Ok(pi(Mult::Omega, a, b))
            }
            ExprKind::Call(f, args) | ExprKind::TypeApp(f, args) => {
                if let Some(p) = path_name(f) {
                    if self.rec.as_ref().is_some_and(|r| r.name == p) {
                        return self.elab_rec_call(args, exp, e.span);
                    }
                }
                let head = match path_name(f).and_then(|p| self.head_of(&p)) {
                    Some(h) => h,
                    None if matches!(f.kind, ExprKind::Var(_)) => {
                        let ExprKind::Var(n) = &f.kind else {
                            unreachable!()
                        };
                        return err(f.span, format!("unknown identifier `{n}`"));
                    }
                    None if matches!(f.kind, ExprKind::Field(..)) => {
                        return err(
                            f.span,
                            "method calls are not supported yet (needs traits, M3b)",
                        );
                    }
                    None => (self.elab(f, None)?, vec![]),
                };
                self.elab_app(head, args.iter().map(Arg::Expr).collect(), exp, e.span)
            }
            ExprKind::Block(b) => self.elab_block(b, exp),
            ExprKind::Do(b) => self.elab_do(b, exp, e.span),
            ExprKind::If(cond, then, els) => self.elab_if(cond, then, els.as_deref(), exp, e.span),
            ExprKind::Ref { .. } => err(
                e.span,
                "references are not supported by the elaborator yet (borrow checker, M5)",
            ),
            ExprKind::Match(scrut, arms) => self.elab_match(scrut, arms, exp, e.span),
            ExprKind::Neg(_) => err(e.span, "negation is not supported yet"),
            ExprKind::Str(text) => Ok(str_lit(text)),
        }
    }

    fn elab_field(&mut self, base: &Expr, f: &Ident, exp: Option<&T>, span: Span) -> R<T> {
        let b = self.elab(base, None)?;
        let bt = from_kernel(self.tc.infer(&b), base.span)?;
        let bt = from_kernel(self.tc.whnf(&bt), base.span)?;
        let (h, _) = app_spine(&bt);
        let Term::Const(sname, _) = &*h else {
            return err(
                f.span,
                format!("no field `{}` on type `{}`", f.name, self.pp(&bt)),
            );
        };
        let proj = format!("{sname}.{}", f.name);
        if !matches!(self.env.get(&proj), Some(Decl::Def { .. })) {
            return err(f.span, format!("type `{sname}` has no field `{}`", f.name));
        }
        let head = self.const_term(&proj);
        self.elab_app(head, vec![Arg::Term(b)], exp, span)
    }

    /// Apply `head` to `args`, inserting implicit arguments as metavariables.
    fn elab_app(
        &mut self,
        head: (T, Vec<bool>),
        args: Vec<Arg<'_>>,
        exp: Option<&T>,
        span: Span,
    ) -> R<T> {
        let (mut term, mask) = head;
        let mut fty = from_kernel(self.tc.infer(&term), span)?;
        let mut pending: Vec<(T, usize)> = Vec::new();
        let (mut next, mut i) = (0, 0);
        loop {
            let w = from_kernel(self.tc.whnf(&fty), span)?;
            match &*w {
                Term::Pi(_, d, b) => {
                    let implicit = mask.get(i).copied().unwrap_or(false);
                    if !implicit && next >= args.len() {
                        break;
                    }
                    let mv = self.new_mvar(d.clone(), span);
                    term = app(term, mv.clone());
                    fty = instantiate(b, &mv);
                    i += 1;
                    if !implicit {
                        pending.push((mv, next));
                        next += 1;
                    }
                }
                _ => {
                    if next < args.len() {
                        return err(
                            span,
                            format!("too many arguments: `{}` is not a function", self.pp(&term)),
                        );
                    }
                    break;
                }
            }
        }
        // use the expected type to solve implicit arguments before elaborating the explicit ones
        if let (Some(exp), true) = (exp, next == args.len()) {
            let snap = self.tc.snapshot();
            if !from_kernel(self.tc.is_def_eq(&fty, exp), span)? {
                self.tc.restore(snap);
            }
        }
        for (mv, k) in pending {
            let dom = from_kernel(self.tc.infer(&mv), span)?;
            let dom = self.tc.zonk(&dom);
            let a = match &args[k] {
                Arg::Expr(e) => self.elab_check(e, &dom)?,
                Arg::Term(t) => self.coerce(t.clone(), &dom, span)?,
            };
            if !from_kernel(self.tc.is_def_eq(&mv, &a), span)? {
                return err(
                    span,
                    format!(
                        "argument `{}` does not match the expected `{}`",
                        self.pp(&a),
                        self.pp(&mv)
                    ),
                );
            }
        }
        Ok(term)
    }

    fn elab_block(&mut self, b: &Block, exp: Option<&T>) -> R<T> {
        let depth = self.scope.len();
        let mut lets: Vec<(u32, T, T)> = Vec::new();
        for s in &b.stmts {
            match s {
                Stmt::Let { name, ty, init, .. } => {
                    let (val, vty) = match ty {
                        Some(t) => {
                            let t = self.elab_type(t)?;
                            (self.elab_check(init, &t)?, t)
                        }
                        None => {
                            let v = self.elab(init, None)?;
                            let t = from_kernel(self.tc.infer(&v), init.span)?;
                            (v, t)
                        }
                    };
                    let vty = self.tc.zonk(&vty);
                    let x = self.tc.fresh(&name.name, vty.clone(), Mult::Omega);
                    lets.push((x, vty, val));
                    self.scope.push((name.name.clone(), fvar(x)));
                }
                Stmt::Bind { name, .. } => {
                    return err(name.span, "`<-` is only allowed inside a `do` block");
                }
                Stmt::Expr(e) => {
                    let v = self.elab(e, None)?;
                    let t = from_kernel(self.tc.infer(&v), e.span)?;
                    let t = self.tc.zonk(&t);
                    let x = self.tc.fresh("_", t.clone(), Mult::Omega);
                    lets.push((x, t, v));
                }
            }
        }
        let body = match &b.tail {
            Some(t) => self.elab(t, exp)?,
            None => {
                if let Some(exp) = exp {
                    self.coerce(self.unit_value(), exp, b.span)?;
                }
                self.unit_value()
            }
        };
        self.scope.truncate(depth);
        let mut r = self.tc.zonk(&body);
        for (x, ty, val) in lets.into_iter().rev() {
            let (ty, val) = (self.tc.zonk(&ty), self.tc.zonk(&val));
            r = let_(Mult::Omega, ty, val, abstract_fvars(&r, &[x]));
        }
        Ok(r)
    }

    // ---- do notation ----

    fn io_type(&self, a: &T) -> T {
        app(cnst("IO".into(), vec![]), a.clone())
    }

    fn elab_do(&mut self, b: &Block, exp: Option<&T>, span: Span) -> R<T> {
        let r = match exp {
            Some(t) => {
                let w = from_kernel(self.tc.whnf(t), span)?;
                match &*w {
                    Term::App(f, a) if matches!(&**f, Term::Const(n, _) if &**n == "IO") => {
                        a.clone()
                    }
                    Term::MVar(_) => {
                        let l = self.tc.new_level_mvar();
                        let sort_mv = self.new_mvar(sort(l), span);
                        let r = self.new_mvar(sort_mv, span);
                        self.coerce_eq(&w, &self.io_type(&r), span)?;
                        r
                    }
                    _ => {
                        return err(
                            span,
                            format!(
                                "a `do` block has type `IO _`, but `{}` is expected here",
                                self.pp(t)
                            ),
                        )
                    }
                }
            }
            None => {
                let l = self.tc.new_level_mvar();
                let sort_mv = self.new_mvar(sort(l), span);
                self.new_mvar(sort_mv, span)
            }
        };
        self.do_stmts(&b.stmts, b.tail.as_deref(), &r, span)
    }

    fn coerce_eq(&mut self, a: &T, b: &T, span: Span) -> R<()> {
        if from_kernel(self.tc.is_def_eq(a, b), span)? {
            Ok(())
        } else {
            err(
                span,
                format!("type mismatch: `{}` vs `{}`", self.pp(a), self.pp(b)),
            )
        }
    }

    fn do_stmts(&mut self, stmts: &[Stmt], tail: Option<&Expr>, r: &T, span: Span) -> R<T> {
        let bind = |this: &mut Self, a: &T, act: T, k: T| -> T {
            let _ = this;
            mk_apps(
                &cnst("IO.bind".into(), vec![]),
                &[a.clone(), r.clone(), act, k],
            )
        };
        match stmts.split_first() {
            None => match tail {
                Some(t) => self.elab_check(t, &self.io_type(r)),
                None => {
                    let unit = self.unit_type();
                    self.coerce_eq(r, &unit, span)?;
                    Ok(mk_apps(
                        &cnst("IO.pure".into(), vec![]),
                        &[unit, self.unit_value()],
                    ))
                }
            },
            Some((Stmt::Bind { name, ty, action }, rest)) => {
                let a = match ty {
                    Some(t) => self.elab_type(t)?,
                    None => self.fresh_type(action.span),
                };
                let act = self.elab_check(action, &self.io_type(&a))?;
                let a = self.tc.zonk(&a);
                let x = self.tc.fresh(&name.name, a.clone(), Mult::Omega);
                self.scope.push((name.name.clone(), fvar(x)));
                let body = self.do_stmts(rest, tail, r, span);
                self.scope.pop();
                let lam = self.close_lam(x, &body?);
                Ok(bind(self, &a, act, lam))
            }
            Some((Stmt::Expr(e), rest)) => {
                let a = self.fresh_type(e.span);
                let act = self.elab_check(e, &self.io_type(&a))?;
                let a = self.tc.zonk(&a);
                let x = self.tc.fresh("_", a.clone(), Mult::Omega);
                let body = self.do_stmts(rest, tail, r, span)?;
                let lam = self.close_lam(x, &body);
                Ok(bind(self, &a, act, lam))
            }
            Some((Stmt::Let { name, ty, init, .. }, rest)) => {
                let (val, vty) = match ty {
                    Some(t) => {
                        let t = self.elab_type(t)?;
                        (self.elab_check(init, &t)?, t)
                    }
                    None => {
                        let v = self.elab(init, None)?;
                        let t = from_kernel(self.tc.infer(&v), init.span)?;
                        (v, t)
                    }
                };
                let vty = self.tc.zonk(&vty);
                let x = self.tc.fresh(&name.name, vty.clone(), Mult::Omega);
                self.scope.push((name.name.clone(), fvar(x)));
                let body = self.do_stmts(rest, tail, r, span);
                self.scope.pop();
                let body = self.tc.zonk(&body?);
                let val = self.tc.zonk(&val);
                Ok(let_(Mult::Omega, vty, val, abstract_fvars(&body, &[x])))
            }
        }
    }

    fn fresh_type(&mut self, span: Span) -> T {
        let l = self.tc.new_level_mvar();
        let s = self.new_mvar(sort(l), span);
        self.new_mvar(s, span)
    }

    /// `fun x => body` with `x` a local variable.
    fn close_lam(&mut self, x: u32, body: &T) -> T {
        self.tc.zonk_locals();
        let body = self.tc.zonk(body);
        self.tc.mk_lam(&[x], &body)
    }

    // ---- pattern matching ----

    fn global_ctor(&self, name: &str) -> Option<String> {
        let full = self
            .aliases
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.to_string());
        matches!(self.env.get(&full), Some(Decl::Ctor(_))).then_some(full)
    }

    fn elab_pattern(&self, e: &Expr) -> R<Pat> {
        match &e.kind {
            ExprKind::Wild => Ok(Pat::Wild),
            ExprKind::Var(n) => Ok(match self.global_ctor(n) {
                Some(full) => Pat::Ctor(full, vec![]),
                None => Pat::Var(n.clone()),
            }),
            ExprKind::Field(..) => match path_name(e).and_then(|p| self.global_ctor(&p)) {
                Some(full) => Ok(Pat::Ctor(full, vec![])),
                None => err(e.span, "unknown constructor in pattern"),
            },
            ExprKind::Nat(0) => Ok(Pat::Ctor("Nat.zero".into(), vec![])),
            ExprKind::Nat(k) => {
                let inner = self.elab_pattern(&Expr {
                    kind: ExprKind::Nat(k - 1),
                    span: e.span,
                })?;
                Ok(Pat::Ctor("Nat.succ".into(), vec![inner]))
            }
            ExprKind::Call(f, args) => {
                let Some(full) = path_name(f).and_then(|p| self.global_ctor(&p)) else {
                    return err(f.span, "unknown constructor in pattern");
                };
                let subs = args
                    .iter()
                    .map(|a| self.elab_pattern(a))
                    .collect::<R<Vec<_>>>()?;
                Ok(Pat::Ctor(full, subs))
            }
            _ => err(e.span, "this kind of pattern is not supported yet"),
        }
    }

    fn elab_match(&mut self, scrut: &Expr, arms: &[Arm], exp: Option<&T>, span: Span) -> R<T> {
        let ret = match exp {
            Some(t) => t.clone(),
            None => {
                let l = self.tc.new_level_mvar();
                let s = self.new_mvar(sort(l), span);
                self.new_mvar(s, span)
            }
        };
        let s = self.elab(scrut, None)?;
        let s = self.tc.zonk(&s);
        let (x, wrap) = match &*s {
            Term::FVar(id) => (*id, None),
            _ => {
                let ty = from_kernel(self.tc.infer(&s), scrut.span)?;
                let ty = self.tc.zonk(&ty);
                (
                    self.tc.fresh("m", ty.clone(), Mult::Omega),
                    Some((ty, s.clone())),
                )
            }
        };
        let mut rows = Vec::new();
        for a in arms {
            rows.push(Row {
                pats: vec![self.elab_pattern(&a.pat)?],
                binds: vec![],
                body: &a.body,
            });
        }
        let top = match &mut self.rec {
            Some(rc) if rc.decr == x && !rc.in_top => {
                rc.in_top = true;
                true
            }
            _ => false,
        };
        let r = self.compile_match(vec![x], rows, &ret, top, span);
        if top {
            if let Some(rc) = &mut self.rec {
                rc.in_top = false;
            }
        }
        let r = r?;
        Ok(match wrap {
            None => r,
            Some((ty, val)) => {
                let r = self.tc.zonk(&r);
                let_(Mult::Omega, ty, val, abstract_fvars(&r, &[x]))
            }
        })
    }

    /// Decision-tree compilation of a pattern matrix into recursor applications.
    fn compile_match(
        &mut self,
        cols: Vec<u32>,
        rows: Vec<Row<'_>>,
        ret: &T,
        top: bool,
        span: Span,
    ) -> R<T> {
        let Some(first) = rows.first() else {
            return err(span, "non-exhaustive patterns");
        };
        let Some(j) = first.pats.iter().position(|p| matches!(p, Pat::Ctor(..))) else {
            // leaf: bind variables and elaborate the arm
            let depth = self.scope.len();
            for (n, t) in &first.binds {
                self.scope.push((n.clone(), t.clone()));
            }
            for (p, &c) in first.pats.iter().zip(&cols) {
                if let Pat::Var(n) = p {
                    self.scope.push((n.clone(), fvar(c)));
                }
            }
            let r = self.elab_check(first.body, ret);
            self.scope.truncate(depth);
            return r;
        };
        let x = cols[j];
        let xty = from_kernel(self.tc.local_ty(x), span)?;
        let xty = from_kernel(self.tc.whnf(&xty), span)?;
        let (head, targs) = app_spine(&xty);
        let Term::Const(iname, ilevels) = &*head else {
            return err(
                span,
                format!("cannot match on a value of type `{}`", self.pp(&xty)),
            );
        };
        let Some(Decl::Inductive(info)) = self.env.get(iname) else {
            return err(
                span,
                format!("cannot match on a value of type `{}`", self.pp(&xty)),
            );
        };
        if info.nindices > 0 {
            return err(span, "matching on indexed families is not supported yet");
        }
        let (ctors, ind_nlevels): (Vec<String>, usize) = (
            info.ctors.iter().map(|c| c.to_string()).collect(),
            info.lparams.len(),
        );
        let params = targs[..info.nparams].to_vec();
        let iname = iname.to_string();
        let ilevels = ilevels.clone();

        // motive: fun (t : I params) => ret[x := t], generalizing the other
        // parameters when this is the top-level split of a recursive function
        let others: Vec<u32> = match (&self.rec, top) {
            (Some(rc), true) => rc
                .explicit
                .iter()
                .copied()
                .filter(|&p| p != rc.decr)
                .collect(),
            _ => vec![],
        };
        self.tc.zonk_locals();
        let ret_z = self.tc.zonk(ret);
        let motive_res = self.tc.mk_pi(&others, &ret_z);
        let motive_abs = abstract_fvars(&motive_res, &[x]);
        let ret_abs = abstract_fvars(&ret_z, &[x]);
        let lvl = from_kernel(self.tc.check_is_type(&motive_res), span)?;
        let lvl = self.tc.zonk_level(&lvl);
        let rec_name = format!("{iname}.rec");
        let large = match self.env.get(&rec_name) {
            Some(Decl::Rec(r)) => r.lparams.len() > ind_nlevels,
            _ => return err(span, "missing recursor"),
        };
        let mut rec_levels = ilevels.clone();
        if large {
            rec_levels.insert(0, lvl);
        } else if !lvl.is_zero() {
            return err(
                span,
                format!("`{iname}` can only be matched when the result is a proposition"),
            );
        }
        let motive = lam(Mult::Omega, xty.clone(), motive_abs.clone());

        let mut minors = Vec::new();
        for cname in &ctors {
            let cty = from_kernel(self.env.const_type(cname, &ilevels), span)?;
            let rest = from_kernel(self.tc.instantiate_pis(&cty, &params), span)?;
            let (fields, _) = from_kernel(self.tc.telescope(&rest, None), span)?;
            let fterms: Vec<T> = fields.iter().map(|&f| fvar(f)).collect();
            let ctor_app = mk_apps(
                &cnst(cname.as_str().into(), ilevels.clone()),
                &[params.clone(), fterms].concat(),
            );
            let ret_c = instantiate(&ret_abs, &ctor_app);

            // induction hypotheses for recursive fields
            let mut ihs = Vec::new();
            for &f in &fields {
                let fty = from_kernel(self.tc.local_ty(f), span)?;
                if !contains_const(&fty, &iname) {
                    continue;
                }
                let (xs, _) = from_kernel(self.tc.telescope(&fty, None), span)?;
                let applied = mk_apps(&fvar(f), &xs.iter().map(|&v| fvar(v)).collect::<Vec<_>>());
                let ih_res = instantiate(&motive_abs, &applied);
                let ih_ty = self.tc.mk_pi(&xs, &ih_res);
                let ih = self.tc.fresh("ih", ih_ty, Mult::Omega);
                if top {
                    if let Some(rc) = &mut self.rec {
                        rc.fields.insert(f, fvar(ih));
                    }
                }
                ihs.push(ih);
            }

            // specialize the rows to this constructor
            let mut new_cols: Vec<u32> = cols[..j].to_vec();
            new_cols.extend(&fields);
            new_cols.extend(&cols[j + 1..]);
            let mut new_rows = Vec::new();
            for row in &rows {
                let (before, after) = (&row.pats[..j], &row.pats[j + 1..]);
                let mut binds = row.binds.clone();
                let mid: Vec<Pat> = match &row.pats[j] {
                    Pat::Ctor(c, subs) if c == cname => {
                        if subs.len() != fields.len() {
                            return err(
                                span,
                                format!(
                                    "constructor `{cname}` takes {} fields, the pattern has {}",
                                    fields.len(),
                                    subs.len()
                                ),
                            );
                        }
                        subs.clone()
                    }
                    Pat::Ctor(..) => continue,
                    Pat::Var(n) => {
                        binds.push((n.clone(), ctor_app.clone()));
                        vec![Pat::Wild; fields.len()]
                    }
                    Pat::Wild => vec![Pat::Wild; fields.len()],
                };
                let pats = [before, &mid[..], after].concat();
                new_rows.push(Row {
                    pats,
                    binds,
                    body: row.body,
                });
            }
            if new_rows.is_empty() {
                return err(span, format!("non-exhaustive patterns: missing `{cname}`"));
            }
            // inside the branch the scrutinee *is* the constructor application
            let xt = fvar(x);
            let saved = self.scope.clone();
            for (_, t) in self.scope.iter_mut() {
                if *t == xt {
                    *t = ctor_app.clone();
                }
            }
            let sub = self.compile_match(new_cols, new_rows, &ret_c, false, span);
            self.scope = saved;
            let sub = sub?;
            self.tc.zonk_locals();
            let sub = self.tc.zonk(&sub);
            let body = if top {
                self.tc.mk_lam(&others, &sub)
            } else {
                sub
            };
            let binders: Vec<u32> = fields.iter().chain(&ihs).copied().collect();
            minors.push(self.tc.mk_lam(&binders, &body));
        }
        let mut args = params;
        args.push(motive);
        args.extend(minors);
        args.push(fvar(x));
        args.extend(others.iter().map(|&o| fvar(o)));
        Ok(mk_apps(&cnst(rec_name.as_str().into(), rec_levels), &args))
    }

    /// `f(args)` inside the body of a structurally recursive `f`: becomes the
    /// induction hypothesis of the matched parameter's field.
    fn elab_rec_call(&mut self, args: &[Expr], exp: Option<&T>, span: Span) -> R<T> {
        let rc = self.rec.as_ref().expect("recursion context");
        let (decr, explicit) = (rc.decr, rc.explicit.clone());
        if args.len() != explicit.len() {
            return err(
                span,
                "a recursive call must supply all of the function's arguments",
            );
        }
        let k = explicit
            .iter()
            .position(|&p| p == decr)
            .expect("decreasing parameter is explicit");
        let dty = from_kernel(self.tc.local_ty(decr), span)?;
        let arg = self.elab_check(&args[k], &dty)?;
        let arg = self.tc.zonk(&arg);
        let ih = match &*arg {
            Term::FVar(f) => self.rec.as_ref().and_then(|rc| rc.fields.get(f).cloned()),
            _ => None,
        };
        let Some(ih) = ih else {
            return err(
                args[k].span,
                "this recursive call is not structural: its argument must be a field bound by matching on the parameter",
            );
        };
        let rest: Vec<Arg> = args
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != k)
            .map(|(_, a)| Arg::Expr(a))
            .collect();
        self.elab_app((ih, vec![]), rest, exp, span)
    }

    fn elab_if(
        &mut self,
        cond: &Expr,
        then: &Block,
        els: Option<&Expr>,
        exp: Option<&T>,
        span: Span,
    ) -> R<T> {
        let bool_ty = cnst("Bool".into(), vec![]);
        let c = self.elab_check(cond, &bool_ty)?;
        let then_t = self.elab_block(then, exp)?;
        let ty = match exp {
            Some(t) => t.clone(),
            None => from_kernel(self.tc.infer(&then_t), then.span)?,
        };
        let then_t = self.coerce(then_t, &ty, then.span)?;
        let else_t = match els {
            Some(e) => self.elab_check(e, &ty)?,
            None => self.coerce(self.unit_value(), &ty, span)?,
        };
        let ty = self.tc.zonk(&ty);
        let lvl = from_kernel(self.tc.check_is_type(&ty), span)?;
        let lvl = self.tc.zonk_level(&lvl);
        let motive = lam(Mult::Omega, bool_ty, ty);
        let rec = cnst("Bool.rec".into(), vec![lvl]);
        // Bool.rec motive (false case) (true case) major
        Ok(mk_apps(&rec, &[motive, else_t, then_t, c]))
    }
}

fn mentions_expr(e: &Expr, name: &str) -> bool {
    match &e.kind {
        ExprKind::Var(n) => n == name,
        ExprKind::Nat(_) | ExprKind::Str(_) | ExprKind::Wild | ExprKind::Unit => false,
        ExprKind::Neg(a) => mentions_expr(a, name),
        ExprKind::Binary(_, a, b) | ExprKind::Arrow(a, b) => {
            mentions_expr(a, name) || mentions_expr(b, name)
        }
        ExprKind::Ref { inner, .. } => mentions_expr(inner, name),
        ExprKind::Call(f, args) | ExprKind::TypeApp(f, args) => {
            mentions_expr(f, name) || args.iter().any(|a| mentions_expr(a, name))
        }
        ExprKind::Field(b, _) => mentions_expr(b, name),
        ExprKind::Block(b) | ExprKind::Do(b) => mentions_block(b, name),
        ExprKind::If(c, t, e) => {
            mentions_expr(c, name)
                || mentions_block(t, name)
                || e.as_ref().is_some_and(|e| mentions_expr(e, name))
        }
        ExprKind::Match(s, arms) => {
            mentions_expr(s, name) || arms.iter().any(|a| mentions_expr(&a.body, name))
        }
    }
}

fn mentions_block(b: &Block, name: &str) -> bool {
    b.stmts.iter().any(|s| match s {
        Stmt::Let { init, .. } => mentions_expr(init, name),
        Stmt::Bind { action, .. } => mentions_expr(action, name),
        Stmt::Expr(e) => mentions_expr(e, name),
    }) || b.tail.as_ref().is_some_and(|t| mentions_expr(t, name))
}
