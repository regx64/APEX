//! The borrow checker proper.
//!
//! Code is structured and loop-free (recursion instead), so NLL reduces to
//! liveness: a borrow lasts while the variable holding the reference is still
//! used later. Pass 1 walks the body to learn each variable's last use; pass 2
//! walks it again, in the same order, checking every access against the borrows
//! that are live at that point.

use crate::sig::{param_kind, Callee, ParamKind, RetKind};
use apex_span::Span;
use apex_syntax::ast::*;
use std::collections::HashMap;

/// A borrow-checking error, with Rust's error code and secondary locations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diag {
    pub code: &'static str,
    pub msg: String,
    pub span: Span,
    pub notes: Vec<(Span, String)>,
}

type VarId = usize;
type Place = (VarId, Vec<String>);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Role {
    Local,
    Param,
    /// A `&T` / `&mut T` parameter: data owned by the caller.
    RefParam,
}

#[derive(Clone, Debug)]
struct VarInfo {
    name: String,
    own: bool,
    role: Role,
    /// Borrows this variable's value carries (if it is a reference).
    holds: Vec<usize>,
    is_ref: bool,
    /// `&mut` parameter (a mutable reference that may be reborrowed).
    mut_ref: bool,
    /// Closure nesting depth where it was declared.
    depth: usize,
    param_idx: Option<usize>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum LoanKind {
    Shared,
    Mut,
}

#[derive(Clone, Debug)]
struct Loan {
    place: Place,
    kind: LoanKind,
    /// Held by an expression still being evaluated: alive until the end of the
    /// call or statement.
    temp: bool,
    /// Variables whose value carries this borrow (it lasts while any is still used).
    holders: Vec<VarId>,
    alive: bool,
    span: Span,
    /// A reference parameter's own borrow of the caller's data: never conflicts here.
    external: bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Access {
    Read,
    Assign,
    Move,
    BorrowShared,
    BorrowMut,
}

/// What an expression evaluates to, as far as borrows go.
#[derive(Clone, Default)]
struct Out {
    loans: Vec<usize>,
    is_ref: bool,
}

type Resolver<'r> = &'r dyn Fn(Span) -> Option<Callee>;
type IsCtor<'r> = &'r dyn Fn(&str) -> bool;

struct Checker<'r> {
    resolver: Resolver<'r>,
    is_ctor: IsCtor<'r>,
    callee: Callee,
    pass: u8,
    pos: usize,
    last_use: HashMap<VarId, usize>,
    last_use_span: HashMap<VarId, Span>,
    vars: Vec<VarInfo>,
    scope: Vec<(String, VarId)>,
    moved: HashMap<VarId, Span>,
    loans: Vec<Loan>,
    errors: Vec<Diag>,
    depth: usize,
    /// Variables captured by the closures being walked, innermost last.
    captures: Vec<Vec<VarId>>,
}

/// Check a function body. `callee` is the function's own signature, `resolver`
/// gives the signature of the function called at a call-site span, and
/// `is_ctor` says whether a name in a pattern is a constructor.
pub fn check_fn<'r>(
    f: &FnDecl,
    callee: &Callee,
    resolver: Resolver<'r>,
    is_ctor: IsCtor<'r>,
) -> Vec<Diag> {
    let Some(body) = &f.body else {
        return vec![];
    };
    let mut ck = Checker {
        resolver,
        is_ctor,
        callee: callee.clone(),
        pass: 1,
        pos: 0,
        last_use: HashMap::new(),
        last_use_span: HashMap::new(),
        vars: vec![],
        scope: vec![],
        moved: HashMap::new(),
        loans: vec![],
        errors: vec![],
        depth: 0,
        captures: vec![],
    };
    ck.run(f, body);
    ck.reset();
    ck.pass = 2;
    ck.run(f, body);
    ck.errors
}

impl<'r> Checker<'r> {
    fn reset(&mut self) {
        self.pos = 0;
        self.vars.clear();
        self.scope.clear();
        self.moved.clear();
        self.loans.clear();
        self.errors.clear();
        self.depth = 0;
        self.captures.clear();
    }

    fn error(
        &mut self,
        code: &'static str,
        msg: impl Into<String>,
        span: Span,
        notes: Vec<(Span, String)>,
    ) {
        if self.pass == 2 {
            self.errors.push(Diag {
                code,
                msg: msg.into(),
                span,
                notes,
            });
        }
    }

    fn tick(&mut self) -> usize {
        self.pos += 1;
        self.pos
    }

    fn declare(&mut self, name: &str, info: VarInfo) -> VarId {
        let id = self.vars.len();
        self.vars.push(info);
        self.scope.push((name.to_string(), id));
        id
    }

    fn local(&self, name: &str) -> Option<VarId> {
        self.scope
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, id)| *id)
    }

    fn plain(&self, name: &str) -> VarInfo {
        VarInfo {
            name: name.to_string(),
            own: false,
            role: Role::Local,
            holds: vec![],
            is_ref: false,
            mut_ref: false,
            depth: self.depth,
            param_idx: None,
        }
    }

    fn run(&mut self, f: &FnDecl, body: &Block) {
        for (i, p) in f.params.iter().enumerate() {
            let kind = param_kind(p);
            let mut info = self.plain(&p.name.name);
            info.param_idx = Some(i);
            match kind {
                ParamKind::Own => {
                    info.own = true;
                    info.role = Role::Param;
                }
                ParamKind::Value => info.role = Role::Param,
                ParamKind::Ref | ParamKind::RefMut => {
                    info.role = Role::RefParam;
                    info.is_ref = true;
                    info.mut_ref = kind == ParamKind::RefMut;
                }
            }
            let is_ref = info.is_ref;
            let id = self.declare(&p.name.name, info);
            if is_ref {
                // the caller's data, borrowed for the whole call
                let loan = self.new_loan(
                    (id, vec!["*".into()]),
                    if kind == ParamKind::RefMut {
                        LoanKind::Mut
                    } else {
                        LoanKind::Shared
                    },
                    p.name.span,
                    true,
                );
                self.loans[loan].temp = false;
                self.loans[loan].holders.push(id);
                self.vars[id].holds = vec![loan];
            }
        }
        let out = self.block(body, true);
        self.check_return(body, &out);
    }

    // ---- loans ----

    fn new_loan(&mut self, place: Place, kind: LoanKind, span: Span, external: bool) -> usize {
        self.loans.push(Loan {
            place,
            kind,
            temp: true,
            holders: vec![],
            alive: true,
            span,
            external,
        });
        self.loans.len() - 1
    }

    fn live(&self, l: &Loan, now: usize) -> bool {
        l.alive
            && (l.temp
                || l.holders
                    .iter()
                    .any(|v| self.last_use.get(v).is_some_and(|&u| u > now)))
    }

    fn overlaps(a: &Place, b: &Place) -> bool {
        a.0 == b.0 && (a.1.starts_with(&b.1) || b.1.starts_with(&a.1))
    }

    fn describe(&self, p: &Place) -> String {
        let mut s = self.vars[p.0].name.clone();
        for f in p.1.iter().filter(|f| *f != "*") {
            s.push('.');
            s.push_str(f);
        }
        s
    }

    fn check_access(&mut self, place: &Place, access: Access, span: Span, now: usize) {
        let hit = self
            .loans
            .iter()
            .enumerate()
            .find(|(_, l)| {
                !l.external
                    && self.live(l, now)
                    && Self::overlaps(&l.place, place)
                    && match (access, l.kind) {
                        (Access::Read, LoanKind::Mut) => true,
                        (Access::Read, LoanKind::Shared) => false,
                        (Access::BorrowShared, LoanKind::Shared) => false,
                        _ => true,
                    }
            })
            .map(|(i, _)| i);
        let Some(i) = hit else { return };
        let l = self.loans[i].clone();
        let name = self.describe(place);
        let kind_word = |k: LoanKind| match k {
            LoanKind::Shared => "immutable",
            LoanKind::Mut => "mutable",
        };
        let (code, msg) = match (access, l.kind) {
            (Access::Read, _) => (
                "E0503",
                format!("cannot use `{name}` because it was mutably borrowed"),
            ),
            (Access::Assign, _) => (
                "E0506",
                format!("cannot assign to `{name}` because it is borrowed"),
            ),
            (Access::Move, _) => (
                "E0505",
                format!("cannot move out of `{name}` because it is borrowed"),
            ),
            (Access::BorrowShared, _) => (
                "E0502",
                format!(
                    "cannot borrow `{name}` as immutable because it is also borrowed as mutable"
                ),
            ),
            (Access::BorrowMut, LoanKind::Mut) => (
                "E0499",
                format!("cannot borrow `{name}` as mutable more than once at a time"),
            ),
            (Access::BorrowMut, LoanKind::Shared) => (
                "E0502",
                format!(
                    "cannot borrow `{name}` as mutable because it is also borrowed as immutable"
                ),
            ),
        };
        let mut notes = vec![(
            l.span,
            format!(
                "the {} borrow of `{}` starts here",
                kind_word(l.kind),
                self.describe(&l.place)
            ),
        )];
        if let Some(&v) = l
            .holders
            .iter()
            .find(|v| self.last_use.get(v).is_some_and(|&u| u > now))
        {
            if let Some(&sp) = self.last_use_span.get(&v) {
                notes.push((
                    sp,
                    format!(
                        "the borrow is used again here, through `{}`",
                        self.vars[v].name
                    ),
                ));
            }
        }
        self.error(code, msg, span, notes);
    }

    fn check_moved(&mut self, v: VarId, span: Span) {
        if let Some(&at) = self.moved.get(&v) {
            let name = self.vars[v].name.clone();
            self.error(
                "E0382",
                format!("use of moved value `{name}`"),
                span,
                vec![(at, format!("`{name}` is an `own` value: it was moved here"))],
            );
        }
    }

    fn use_var(&mut self, v: VarId, pos: usize, span: Span) {
        if self.pass == 1 {
            self.last_use.insert(v, pos);
            self.last_use_span.insert(v, span);
        }
        // a closure that mentions an outer variable captures it
        let depth = self.vars[v].depth;
        for (i, set) in self.captures.iter_mut().enumerate() {
            if i + 1 > depth && !set.contains(&v) {
                set.push(v);
            }
        }
    }

    // ---- places ----

    fn place_of(&self, e: &Expr) -> Option<Place> {
        match &e.kind {
            ExprKind::Var(n) => self.local(n).map(|v| (v, vec![])),
            ExprKind::Field(b, f) => self.place_of(b).map(|(v, mut p)| {
                p.push(f.name.clone());
                (v, p)
            }),
            ExprKind::Deref(b) => self.place_of(b),
            _ => None,
        }
    }

    /// `&place` or `&mut place`.
    fn borrow(&mut self, place: Place, mutable: bool, span: Span) -> Out {
        let pos = self.tick();
        self.use_var(place.0, pos, span);
        self.check_moved(place.0, span);
        let info = self.vars[place.0].clone();
        if info.own {
            self.error(
                "APEX",
                format!("cannot borrow the `own` value `{}` yet: borrowing a linear value is not supported", info.name),
                span,
                vec![],
            );
        }
        if mutable && info.role == Role::RefParam && !info.mut_ref {
            self.error(
                "E0596",
                format!(
                    "cannot borrow `{}` as mutable, as it is behind a `&` reference",
                    info.name
                ),
                span,
                vec![],
            );
        }
        let access = if mutable {
            Access::BorrowMut
        } else {
            Access::BorrowShared
        };
        self.check_access(&place, access, span, pos);
        let id = self.new_loan(
            place,
            if mutable {
                LoanKind::Mut
            } else {
                LoanKind::Shared
            },
            span,
            false,
        );
        // a reborrow keeps what it was derived from alive
        let mut loans = vec![id];
        loans.extend(info.holds.iter().copied());
        Out {
            loans,
            is_ref: true,
        }
    }

    // ---- expressions ----

    fn var_use(&mut self, name: &str, span: Span, consume: bool) -> Out {
        let Some(v) = self.local(name) else {
            return Out::default(); // a global
        };
        let pos = self.tick();
        self.use_var(v, pos, span);
        self.check_moved(v, span);
        self.check_access(&(v, vec![]), Access::Read, span, pos);
        let info = self.vars[v].clone();
        if info.own && self.depth > info.depth {
            self.error(
                "APEX",
                format!("the `own` value `{name}` cannot be captured by a closure yet"),
                span,
                vec![],
            );
        }
        if consume && info.own {
            self.check_access(&(v, vec![]), Access::Move, span, pos);
            self.moved.insert(v, span);
        }
        Out {
            loans: info.holds,
            is_ref: info.is_ref,
        }
    }

    fn expr(&mut self, e: &Expr, consume: bool) -> Out {
        match &e.kind {
            ExprKind::Nat(_) | ExprKind::Str(_) | ExprKind::Wild | ExprKind::Unit => Out::default(),
            ExprKind::Var(n) => self.var_use(n, e.span, consume),
            ExprKind::Field(..) | ExprKind::Deref(_) => match self.place_of(e) {
                Some(place) => {
                    let pos = self.tick();
                    self.use_var(place.0, pos, e.span);
                    self.check_moved(place.0, e.span);
                    self.check_access(&place, Access::Read, e.span, pos);
                    Out::default()
                }
                None => {
                    if let ExprKind::Field(b, _) | ExprKind::Deref(b) = &e.kind {
                        self.expr(b, false);
                    }
                    Out::default()
                }
            },
            ExprKind::Ref { mutable, inner, .. } => match self.place_of(inner) {
                Some(place) => self.borrow(place, *mutable, e.span),
                None => {
                    let out = self.expr(inner, true);
                    if *mutable {
                        self.error(
                            "APEX",
                            "cannot take `&mut` of a temporary value",
                            e.span,
                            vec![],
                        );
                    }
                    Out {
                        loans: out.loans,
                        is_ref: true,
                    }
                }
            },
            ExprKind::Neg(a) => self.expr(a, true),
            ExprKind::Arrow(..) => Out::default(),
            ExprKind::Binary(_, l, r) => {
                let callee = (self.resolver)(e.span);
                self.call(callee.as_ref(), None, &[&**l, &**r])
            }
            ExprKind::Call(f, args) | ExprKind::TypeApp(f, args) => self.call_expr(e, f, args),
            ExprKind::Block(b) | ExprKind::Do(b) => self.block(b, consume),
            ExprKind::If(c, t, els) => {
                self.expr(c, true);
                let (moved0, n0) = (self.moved.clone(), self.loans.len());
                let o1 = self.block(t, true);
                let moved1 = std::mem::replace(&mut self.moved, moved0);
                let o2 = match els {
                    Some(x) => self.expr(x, true),
                    None => Out::default(),
                };
                self.merge_moved(moved1);
                let out = join(o1, o2);
                // only what the value carries outlives the branches
                self.kill_temps(n0, &out);
                out
            }
            ExprKind::Match(s, arms) => {
                let scrut_consume = !self.yields_ref(s);
                self.expr(s, scrut_consume);
                let (moved0, n0) = (self.moved.clone(), self.loans.len());
                let mut result = Out::default();
                let mut all_moved = moved0.clone();
                for a in arms {
                    self.moved = moved0.clone();
                    let mark = self.scope.len();
                    self.bind_pattern(&a.pat);
                    let o = self.expr(&a.body, true);
                    self.scope.truncate(mark);
                    for (k, v) in self.moved.clone() {
                        all_moved.insert(k, v);
                    }
                    result = join(result, o);
                }
                self.moved = all_moved;
                self.kill_temps(n0, &result);
                result
            }
            ExprKind::List(items) => {
                for i in items {
                    self.expr(i, true);
                }
                Out::default()
            }
            ExprKind::Lambda { params, body } => {
                self.depth += 1;
                self.captures.push(vec![]);
                let mark = self.scope.len();
                for p in params {
                    let info = self.plain(&p.name.name);
                    self.declare(&p.name.name, info);
                }
                self.expr(body, true);
                self.scope.truncate(mark);
                let captured = self.captures.pop().unwrap_or_default();
                self.depth -= 1;
                // the closure carries what its captured references carry
                let mut loans = Vec::new();
                for v in captured {
                    loans.extend(self.vars[v].holds.iter().copied());
                }
                Out {
                    is_ref: !loans.is_empty(),
                    loans,
                }
            }
            ExprKind::For { var, iter, body } => {
                self.expr(iter, true);
                self.depth += 1;
                self.captures.push(vec![]);
                let mark = self.scope.len();
                let info = self.plain(&var.name);
                self.declare(&var.name, info);
                self.block(body, true);
                self.scope.truncate(mark);
                self.captures.pop();
                self.depth -= 1;
                Out::default()
            }
        }
    }

    fn kill_temps(&mut self, from: usize, keep: &Out) {
        for id in from..self.loans.len() {
            if self.loans[id].temp && !keep.loans.contains(&id) {
                self.loans[id].alive = false;
            }
        }
    }

    fn merge_moved(&mut self, other: HashMap<VarId, Span>) {
        for (k, v) in other {
            self.moved.entry(k).or_insert(v);
        }
    }

    /// Declare the variables a pattern binds (constructors are not variables).
    fn bind_pattern(&mut self, pat: &Expr) {
        match &pat.kind {
            ExprKind::Var(n) if !(self.is_ctor)(n) => {
                let info = self.plain(n);
                self.declare(n, info);
            }
            ExprKind::Call(_, args) => args.iter().for_each(|a| self.bind_pattern(a)),
            _ => {}
        }
    }

    fn yields_ref(&self, e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Ref { .. } => true,
            ExprKind::Var(n) => self.local(n).is_some_and(|v| self.vars[v].is_ref),
            ExprKind::Call(..) | ExprKind::Binary(..) => matches!(
                (self.resolver)(e.span).map(|c| c.ret),
                Some(RetKind::Ref(_))
            ),
            ExprKind::Block(b) => b.tail.as_ref().is_some_and(|t| self.yields_ref(t)),
            ExprKind::If(_, t, Some(els)) => {
                t.tail.as_ref().is_some_and(|x| self.yields_ref(x)) && self.yields_ref(els)
            }
            ExprKind::Match(_, arms) => {
                !arms.is_empty() && arms.iter().all(|a| self.yields_ref(&a.body))
            }
            _ => false,
        }
    }

    // ---- calls ----

    fn call_expr(&mut self, e: &Expr, f: &Expr, args: &[Expr]) -> Out {
        let callee = (self.resolver)(e.span);
        let arg_refs: Vec<&Expr> = args.iter().collect();
        if let ExprKind::Field(base, _) = &f.kind {
            let is_method = callee
                .as_ref()
                .is_some_and(|c| c.params.len() == args.len() + 1);
            if is_method {
                return self.call(callee.as_ref(), Some(base), &arg_refs);
            }
        }
        // a call of a local (a closure) uses that variable
        if matches!(&f.kind, ExprKind::Var(_) | ExprKind::Field(..)) {
            if self.place_of(f).is_some() {
                self.expr(f, false);
            }
        } else {
            self.expr(f, false);
        }
        self.call(callee.as_ref(), None, &arg_refs)
    }

    fn call(&mut self, callee: Option<&Callee>, recv: Option<&Expr>, args: &[&Expr]) -> Out {
        let mut all: Vec<&Expr> = Vec::new();
        if let Some(r) = recv {
            all.push(r);
        }
        all.extend(args.iter().copied());
        let kinds: Vec<ParamKind> = (0..all.len())
            .map(|i| {
                callee
                    .and_then(|c| c.params.get(i))
                    .copied()
                    .unwrap_or(ParamKind::Value)
            })
            .collect();
        let mark = self.loans.len();
        // two-phase borrow: `v.push(v.len())` reads `v` before `&mut v` is activated
        let two_phase = recv.is_some() && kinds.first() == Some(&ParamKind::RefMut);
        let order: Vec<usize> = if two_phase {
            (1..all.len()).chain([0]).collect()
        } else {
            (0..all.len()).collect()
        };
        let mut outs = vec![Out::default(); all.len()];
        for i in order {
            outs[i] = self.arg(all[i], kinds[i], recv.is_some() && i == 0);
        }
        let carried: Vec<usize> = match callee.map(|c| &c.ret) {
            Some(RetKind::Ref(sources)) => sources
                .iter()
                .filter_map(|&i| outs.get(i))
                .flat_map(|o| o.loans.clone())
                .collect(),
            _ => vec![],
        };
        // borrows made for the call end with it, except what the result borrows from
        for id in mark..self.loans.len() {
            if self.loans[id].temp && !carried.contains(&id) {
                self.loans[id].alive = false;
            }
        }
        Out {
            is_ref: matches!(callee.map(|c| &c.ret), Some(RetKind::Ref(_))),
            loans: carried,
        }
    }

    fn arg(&mut self, e: &Expr, kind: ParamKind, is_recv: bool) -> Out {
        match kind {
            ParamKind::Ref => {
                if is_recv {
                    return match self.place_of(e) {
                        Some(p) => self.borrow(p, false, e.span),
                        None => self.expr(e, false),
                    };
                }
                if !self.yields_ref(e) {
                    self.error(
                        "E0308",
                        "expected a reference, found a value: write `&` before the argument",
                        e.span,
                        vec![],
                    );
                }
                self.expr(e, false)
            }
            ParamKind::RefMut => {
                if is_recv {
                    return match self.place_of(e) {
                        Some(p) => self.borrow(p, true, e.span),
                        None => self.expr(e, false),
                    };
                }
                if matches!(&e.kind, ExprKind::Ref { mutable: true, .. }) {
                    return self.expr(e, false);
                }
                // passing a `&mut` variable on is an implicit reborrow
                match self.place_of(e) {
                    Some(p) if self.vars[p.0].mut_ref => self.borrow(p, true, e.span),
                    _ => {
                        self.error(
                            "E0308",
                            "expected a mutable reference: write `&mut place`",
                            e.span,
                            vec![],
                        );
                        self.expr(e, false)
                    }
                }
            }
            ParamKind::Own | ParamKind::Value => {
                let own_var = match &e.kind {
                    ExprKind::Var(n) => self.local(n).filter(|&v| self.vars[v].own),
                    _ => None,
                };
                let out = self.expr(e, true);
                if let (ParamKind::Value, Some(v)) = (kind, own_var) {
                    let name = self.vars[v].name.clone();
                    self.error(
                        "APEX",
                        format!(
                            "the `own` value `{name}` can only be passed to an `own` parameter"
                        ),
                        e.span,
                        vec![],
                    );
                }
                out
            }
        }
    }

    // ---- blocks and statements ----

    fn block(&mut self, b: &Block, consume: bool) -> Out {
        let (mark, nvars) = (self.scope.len(), self.vars.len());
        for s in &b.stmts {
            self.stmt(s);
        }
        let out = match &b.tail {
            Some(t) => self.expr(t, consume),
            None => Out::default(),
        };
        self.scope.truncate(mark);
        // borrows held by variables of this block end with it, unless the value carries them out
        for id in 0..self.loans.len() {
            let l = &mut self.loans[id];
            if l.external || !l.holders.iter().any(|&v| v >= nvars) {
                continue;
            }
            l.holders.retain(|&v| v < nvars);
            if out.loans.contains(&id) {
                l.temp = true;
            } else if l.holders.is_empty() && !l.temp {
                l.alive = false;
            }
        }
        out
    }

    fn bind(&mut self, name: &str, init: &Out, own: bool) -> VarId {
        let mut info = self.plain(name);
        info.own = own;
        info.is_ref = init.is_ref;
        info.holds = init.loans.clone();
        let v = self.declare(name, info);
        for &l in &init.loans {
            let loan = &mut self.loans[l];
            loan.temp = false;
            if !loan.holders.contains(&v) {
                loan.holders.push(v);
            }
        }
        v
    }

    fn stmt(&mut self, s: &Stmt) {
        let mark = self.loans.len();
        match s {
            Stmt::Let { name, init, .. } => {
                if let ExprKind::Ref { mutable: true, .. } = &init.kind {
                    self.error(
                        "APEX",
                        "storing a `&mut` reference in a variable is not supported yet: pass `&mut place` directly to a function",
                        init.span,
                        vec![],
                    );
                }
                let out = self.expr(init, true);
                if let ExprKind::Var(n) = &init.kind {
                    if self.local(n).is_some_and(|v| self.vars[v].own) {
                        self.error(
                            "APEX",
                            format!("cannot bind the `own` value `{n}` to a variable yet: pass it directly to an `own` parameter"),
                            init.span,
                            vec![],
                        );
                    }
                }
                self.bind(&name.name, &out, false);
                self.kill_temps(mark, &out);
            }
            Stmt::Bind { name, action, .. } => {
                let out = self.expr(action, true);
                self.bind(&name.name, &Out::default(), false);
                self.kill_temps(mark, &out);
            }
            Stmt::Assign { target, op, value } => {
                let out = self.expr(value, true);
                if op.is_some() {
                    self.expr(target, false);
                }
                if let Some(place) = self.place_of(target) {
                    let pos = self.tick();
                    self.use_var(place.0, pos, target.span);
                    let info = self.vars[place.0].clone();
                    if info.role == Role::RefParam && !info.mut_ref {
                        self.error(
                            "E0594",
                            format!(
                                "cannot assign to data behind the `&` reference `{}`",
                                info.name
                            ),
                            target.span,
                            vec![],
                        );
                    }
                    self.check_access(&place, Access::Assign, target.span, pos);
                }
                self.kill_temps(mark, &out);
            }
            Stmt::Expr(e) => {
                let out = self.expr(e, true);
                self.kill_temps(mark, &out);
                // the value is discarded: whatever it borrowed ends here
                for l in &out.loans {
                    if self.loans[*l].temp {
                        self.loans[*l].alive = false;
                    }
                }
            }
        }
    }

    // ---- returns ----

    fn check_return(&mut self, body: &Block, out: &Out) {
        let RetKind::Ref(sources) = self.callee.ret.clone() else {
            return;
        };
        let span = body.tail.as_ref().map_or(body.span, |t| t.span);
        for &id in &out.loans {
            let l = self.loans[id].clone();
            let info = self.vars[l.place.0].clone();
            if info.role == Role::RefParam {
                let idx = info.param_idx.unwrap_or(usize::MAX);
                if !sources.contains(&idx) {
                    self.error(
                        "E0621",
                        format!(
                            "the returned reference borrows from the parameter `{}`, but the signature ties the result to another parameter",
                            info.name
                        ),
                        span,
                        vec![],
                    );
                    return;
                }
            } else {
                self.error(
                    "E0515",
                    format!(
                        "cannot return a reference to the local variable `{}`",
                        self.describe(&l.place)
                    ),
                    span,
                    vec![(
                        l.span,
                        format!(
                            "`{}` is borrowed here, but it is dropped at the end of the function",
                            info.name
                        ),
                    )],
                );
                return;
            }
        }
    }
}

fn join(mut a: Out, b: Out) -> Out {
    for l in b.loans {
        if !a.loans.contains(&l) {
            a.loans.push(l);
        }
    }
    a.is_ref |= b.is_ref;
    a
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sig::callee_of;
    use apex_syntax::parse;

    /// Check the function named `test` in `src`. Callees are the other functions
    /// of the file, found by name (a method call resolves by the method's name).
    fn check(src: &str) -> Vec<Diag> {
        let m = parse(src).unwrap_or_else(|e| panic!("parse: {}", e.msg));
        let mut table: HashMap<String, Callee> = HashMap::new();
        let mut target = None;
        for item in &m.items {
            let fns: Vec<&FnDecl> = match &item.kind {
                ItemKind::Fn(f) => vec![f],
                ItemKind::Impl(i) => i.fns.iter().collect(),
                ItemKind::Trait(t) => t.fns.iter().collect(),
                _ => vec![],
            };
            for f in fns {
                let c = callee_of(f, &[]).unwrap_or_else(|e| panic!("sig: {}", e.msg));
                table.insert(f.name.name.clone(), c);
                if f.name.name == "test" {
                    target = Some(f.clone());
                }
            }
        }
        let f = target.expect("a function named `test`");
        let mut spans: HashMap<(u32, u32), Callee> = HashMap::new();
        fn walk(e: &Expr, table: &HashMap<String, Callee>, out: &mut HashMap<(u32, u32), Callee>) {
            if let ExprKind::Call(h, args) = &e.kind {
                let name = match &h.kind {
                    ExprKind::Var(n) => Some(n.clone()),
                    ExprKind::Field(_, m) => Some(m.name.clone()),
                    _ => None,
                };
                if let Some(c) = name.and_then(|n| table.get(&n)) {
                    out.insert((e.span.start, e.span.end), c.clone());
                }
                walk(h, table, out);
                args.iter().for_each(|a| walk(a, table, out));
                return;
            }
            match &e.kind {
                ExprKind::Block(b) | ExprKind::Do(b) => walk_block(b, table, out),
                ExprKind::If(c, t, el) => {
                    walk(c, table, out);
                    walk_block(t, table, out);
                    if let Some(x) = el {
                        walk(x, table, out);
                    }
                }
                ExprKind::Match(s, arms) => {
                    walk(s, table, out);
                    arms.iter().for_each(|a| walk(&a.body, table, out));
                }
                ExprKind::Binary(_, a, b) => {
                    walk(a, table, out);
                    walk(b, table, out);
                }
                ExprKind::Lambda { body, .. } => walk(body, table, out),
                ExprKind::Ref { inner, .. } | ExprKind::Deref(inner) | ExprKind::Neg(inner) => {
                    walk(inner, table, out)
                }
                ExprKind::Field(b, _) => walk(b, table, out),
                ExprKind::List(items) => items.iter().for_each(|a| walk(a, table, out)),
                _ => {}
            }
        }
        fn walk_block(
            b: &Block,
            table: &HashMap<String, Callee>,
            out: &mut HashMap<(u32, u32), Callee>,
        ) {
            for s in &b.stmts {
                match s {
                    Stmt::Let { init, .. } => walk(init, table, out),
                    Stmt::Bind { action, .. } => walk(action, table, out),
                    Stmt::Assign { target, value, .. } => {
                        walk(target, table, out);
                        walk(value, table, out)
                    }
                    Stmt::Expr(e) => walk(e, table, out),
                }
            }
            if let Some(t) = &b.tail {
                walk(t, table, out);
            }
        }
        walk_block(f.body.as_ref().unwrap(), &table, &mut spans);
        let callee = callee_of(&f, &[]).unwrap_or_else(|e| panic!("sig: {}", e.msg));
        let resolver = move |sp: Span| spans.get(&(sp.start, sp.end)).cloned();
        let is_ctor = |n: &str| {
            n.chars().next().is_some_and(char::is_uppercase) || n == "true" || n == "false"
        };
        check_fn(&f, &callee, &resolver, &is_ctor)
    }

    fn codes(src: &str) -> Vec<&'static str> {
        check(src).iter().map(|d| d.code).collect()
    }

    const DECLS: &str = "
        fn take(own x: Nat) -> Nat { x }
        fn read(x: &Nat) -> Nat { 0 }
        fn bump(x: &mut Nat) { }
        fn both(a: &mut Nat, b: &mut Nat) { }
        fn mixed(a: &mut Nat, b: &Nat) { }
        fn first(v: &Nat) -> &Nat { v }
        fn plain(x: Nat) -> Nat { x }
        struct S { a: Nat, b: Nat }
        impl S {
            fn push(&mut self, n: Nat) { }
            fn len(&self) -> Nat { 0 }
        }
    ";

    fn t(body: &str, params: &str) -> Vec<&'static str> {
        codes(&format!("{DECLS} fn test({params}) -> Nat {{ {body} }}"))
    }

    #[test]
    fn clean_programs_pass() {
        assert!(t("let mut x := 1; bump(&mut x); bump(&mut x); x", "").is_empty());
        assert!(t("let x := 1; let r := &x; read(r) + read(&x) + x", "").is_empty());
        assert!(t("let mut s := S.mk(1, 2); s.push(s.len()); s.len()", "").is_empty());
        assert!(t("let mut s := S.mk(1, 2); both(&mut s.a, &mut s.b); 0", "").is_empty());
    }

    #[test]
    fn use_after_move() {
        let ds = check(&format!(
            "{DECLS} fn test(own x: Nat) -> Nat {{ take(x) + take(x) }}"
        ));
        assert_eq!(ds.len(), 1, "{ds:?}");
        assert_eq!(ds[0].code, "E0382");
        assert!(ds[0].msg.contains("use of moved value `x`"));
        assert_eq!(ds[0].notes.len(), 1, "points at where it moved");
        assert_eq!(t("take(x)", "own x: Nat"), Vec::<&str>::new());
    }

    #[test]
    fn moves_are_tracked_across_branches() {
        let src = "if true { take(x); 0 } else { 1 } + take(x)";
        assert_eq!(t(src, "own x: Nat"), vec!["E0382"]);
        // moved in neither branch: fine
        assert!(t("if true { 0 } else { 1 } + take(x)", "own x: Nat").is_empty());
    }

    #[test]
    fn own_value_needs_an_own_parameter() {
        assert_eq!(t("plain(x)", "own x: Nat"), vec!["APEX"]);
        assert_eq!(t("let y := x; 0", "own x: Nat"), vec!["APEX"]);
        assert_eq!(t("read(&x)", "own x: Nat"), vec!["APEX"]);
    }

    #[test]
    fn two_mutable_borrows() {
        let ds = check(&format!(
            "{DECLS} fn test() -> Nat {{ let mut x := 1; both(&mut x, &mut x); x }}"
        ));
        assert_eq!(ds.len(), 1, "{ds:?}");
        assert_eq!(ds[0].code, "E0499");
        assert!(ds[0].msg.contains("more than once"));
    }

    #[test]
    fn mutable_and_shared_borrow() {
        assert_eq!(t("let mut x := 1; mixed(&mut x, &x); x", ""), vec!["E0502"]);
        assert_eq!(
            t("let mut x := 1; let r := &x; bump(&mut x); read(r)", ""),
            vec!["E0502"]
        );
    }

    #[test]
    fn reading_while_mutably_borrowed() {
        assert_eq!(t("let mut x := 1; mixed(&mut x, &x); 0", ""), vec!["E0502"]);
        assert_eq!(
            t("let mut x := 1; mixed(&mut x, x); 0", "").first(),
            Some(&"E0308")
        );
    }

    #[test]
    fn assigning_a_borrowed_variable() {
        let ds = check(&format!(
            "{DECLS} fn test() -> Nat {{ let mut x := 1; let r := &x; x = 2; read(r) }}"
        ));
        assert_eq!(ds.len(), 1, "{ds:?}");
        assert_eq!(ds[0].code, "E0506");
        // the notes show where the borrow starts and where it is used again
        assert_eq!(ds[0].notes.len(), 2, "{:?}", ds[0].notes);
    }

    #[test]
    fn borrows_end_at_their_last_use() {
        // NLL: `r` is dead after `read(r)`, so `x` can change
        assert!(t(
            "let mut x := 1; let r := &x; let a := read(r); x = 2; a + x",
            ""
        )
        .is_empty());
        // a borrow that is never used does not block anything
        assert!(t("let mut x := 1; let r := &x; x = 2; x", "").is_empty());
    }

    #[test]
    fn two_phase_receiver_borrow() {
        // `s.push(s.len())`: the `&mut s` is activated after the arguments are read
        assert!(t("let mut s := S.mk(1, 2); s.push(s.len()); 0", "").is_empty());
    }

    #[test]
    fn reference_arguments_need_ampersand() {
        assert_eq!(t("read(5)", ""), vec!["E0308"]);
        assert_eq!(t("let mut x := 1; bump(x); x", ""), vec!["E0308"]);
        assert_eq!(t("let x := 1; bump(&x); x", ""), vec!["E0308"]);
    }

    #[test]
    fn reborrowing_a_mut_reference_parameter() {
        assert!(t("bump(x); bump(x); 0", "x: &mut Nat").is_empty());
        // but not while it is shared out
        assert_eq!(t("both(x, x); 0", "x: &mut Nat"), vec!["E0499"]);
    }

    #[test]
    fn assigning_through_a_shared_reference() {
        assert_eq!(t("x = 1; 0", "x: &Nat"), vec!["E0594"]);
        assert_eq!(t("bump(x); 0", "x: &Nat"), vec!["E0308"]);
        assert!(t("x = 1; 0", "x: &mut Nat").is_empty());
    }

    #[test]
    fn returning_references() {
        let src = |body: &str, params: &str| {
            codes(&format!("{DECLS} fn test({params}) -> &Nat {{ {body} }}"))
        };
        assert!(src("v", "v: &Nat").is_empty());
        assert!(src("first(v)", "v: &Nat").is_empty());
        assert_eq!(src("let x := 5; &x", "v: &Nat"), vec!["E0515"]);
        assert_eq!(src("&w", "v: &Nat, w: Nat"), vec!["E0515"]);
        let both = codes(&format!(
            "{DECLS} fn test<'a>(v: &'a Nat, w: &Nat) -> &'a Nat {{ w }}"
        ));
        assert_eq!(both, vec!["E0621"]);
    }

    #[test]
    fn mutable_references_are_not_stored() {
        assert_eq!(t("let mut x := 1; let r := &mut x; 0", ""), vec!["APEX"]);
    }

    #[test]
    fn closures_hold_the_borrows_of_what_they_capture() {
        // `f` captures `r`, which borrows `x`: assigning `x` while `f` is still used is an error
        assert_eq!(
            t(
                "let mut x := 1; let r := &x; let f := |n: Nat| read(r) + n; x = 2; f(1)",
                ""
            ),
            vec!["E0506"]
        );
        // an `own` value cannot be captured
        assert_eq!(
            t("let f := |n: Nat| take(x) + n; 0", "own x: Nat"),
            vec!["APEX"]
        );
    }

    #[test]
    fn branches_and_matches() {
        assert!(t("match n { 0 => 1, Nat.succ(m) => m }", "n: Nat").is_empty());
        let src = "match o { None => 0, Some(y) => take(x) } + take(x)";
        assert_eq!(t(src, "own x: Nat, o: Nat"), vec!["E0382"]);
    }
}
