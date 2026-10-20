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
    Local(u32),
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
        let mut aliases = Aliases::new();
        aliases.insert("true".into(), "Bool.true".into());
        aliases.insert("false".into(), "Bool.false".into());
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
        let (ty, val, mask) = {
            let mut cx = self.cx();
            let (fvs, mask) = cx.elab_binders(&f.generics, &f.params)?;
            let ret = match &f.ret {
                Some(t) => cx.elab_type(t)?,
                None => cx.unit_type(),
            };
            let Some(block) = &f.body else {
                return err(f.name.span, "a function needs a body");
            };
            let body = cx.elab_block(block, Some(&ret))?;
            let body = cx.coerce(body, &ret, block.span)?;
            (
                cx.close(&fvs, &ret, true, span)?,
                cx.close(&fvs, &body, false, span)?,
                mask,
            )
        };
        self.add_def(&f.name, ty, val, mask)
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
    scope: Vec<(String, u32)>,
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
            self.scope.push((g.name.name.clone(), id));
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
            self.scope.push((p.name.name.clone(), id));
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
            self.scope.push((f.name.name.clone(), id));
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
        if let Some((_, id)) = self.scope.iter().rev().find(|(n, _)| n == name) {
            return Some(Res::Local(*id));
        }
        if let Some(full) = self.aliases.get(name) {
            return Some(Res::Global(full.clone()));
        }
        self.env.get(name).map(|_| Res::Global(name.to_string()))
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
            Res::Local(id) => Some((fvar(id), vec![])),
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

    fn nat_literal(&self, n: u64, span: Span) -> R<T> {
        if n > 100_000 {
            return err(
                span,
                "integer literals above 100000 are not supported yet (unary Nat)",
            );
        }
        let mut t = cnst("Nat.zero".into(), vec![]);
        for _ in 0..n {
            t = app(cnst("Nat.succ".into(), vec![]), t);
        }
        Ok(t)
    }

    fn elab(&mut self, e: &Expr, exp: Option<&T>) -> R<T> {
        match &e.kind {
            ExprKind::Var(_) | ExprKind::Field(..) => {
                if let Some(path) = path_name(e) {
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
            ExprKind::If(cond, then, els) => self.elab_if(cond, then, els.as_deref(), exp, e.span),
            ExprKind::Ref { .. } => err(
                e.span,
                "references are not supported by the elaborator yet (borrow checker, M5)",
            ),
            ExprKind::Match(..) => err(e.span, "`match` is not supported yet (M3b)"),
            ExprKind::Neg(_) => err(e.span, "negation is not supported yet"),
            ExprKind::Str(_) => err(e.span, "string literals are not supported yet"),
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
                    self.scope.push((name.name.clone(), x));
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
