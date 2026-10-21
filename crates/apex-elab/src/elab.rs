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

/// How an application supplies a binder: written out, inferred by unification,
/// or found by instance search.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Bk {
    Exp,
    Imp,
    Inst,
}

/// A trait bound: the trait's name and its explicit type arguments.
type Bound<'e> = (String, &'e [Expr]);

/// Which binders of a constant's type are implicit.
type Masks = HashMap<String, Vec<Bk>>;
type Aliases = HashMap<String, String>;

/// Trait bookkeeping shared by all declarations.
#[derive(Default)]
struct Tables {
    /// trait name -> its methods (in field order)
    traits: HashMap<String, TraitInfo>,
    /// trait name -> instance definitions
    insts: HashMap<String, Vec<String>>,
    /// method name -> traits declaring it
    methods: HashMap<String, Vec<String>>,
    /// A user definition that shares a name with a prelude one is stored under a
    /// different kernel name; this maps the source name to it.
    shadow: HashMap<String, String>,
}

#[derive(Clone)]
struct TraitInfo {
    /// number of class parameters, `Self` included
    nparams: usize,
    methods: Vec<String>,
    /// names of the trait's own type parameters (after `Self`)
    generics: Vec<String>,
    /// methods that have a default body
    defaults: HashMap<String, FnDecl>,
}

/// An impl under construction: sibling methods already built can be used by
/// later methods, but the impl cannot be used as a whole until it is finished.
struct Pending {
    trait_name: String,
    class_args: Vec<T>,
    built: Vec<Option<T>>,
    /// placeholders for methods not built yet
    holes: Vec<u32>,
    methods: Vec<String>,
}

/// Marker in the error raised when a method needs one that is not built yet.
const NOT_BUILT: &str = "is used before it is defined";

pub struct Elaborator {
    env: Env,
    masks: Masks,
    aliases: Aliases,
    tables: Tables,
    inst_counter: usize,
    /// set once the prelude is loaded: later definitions may shadow prelude names
    prelude_loaded: bool,
    user_defs: std::collections::HashSet<String>,
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
        masks.insert("Eq".into(), vec![Bk::Imp, Bk::Exp, Bk::Exp]);
        masks.insert("Eq.refl".into(), vec![Bk::Imp, Bk::Exp]);
        masks.insert("IO.pure".into(), vec![Bk::Imp, Bk::Exp]);
        masks.insert("List".into(), vec![Bk::Exp]);
        masks.insert("List.nil".into(), vec![Bk::Imp]);
        masks.insert("List.cons".into(), vec![Bk::Imp, Bk::Exp, Bk::Exp]);
        masks.insert("IO.bind".into(), vec![Bk::Imp, Bk::Imp, Bk::Exp, Bk::Exp]);
        let mut aliases = Aliases::new();
        aliases.insert("true".into(), "Bool.true".into());
        aliases.insert("false".into(), "Bool.false".into());
        aliases.insert("print".into(), "IO.print".into());
        aliases.insert("pure".into(), "IO.pure".into());
        let mut el = Elaborator {
            env,
            masks,
            aliases,
            tables: Tables::default(),
            inst_counter: 0,
            prelude_loaded: false,
            user_defs: Default::default(),
        };
        let src = include_str!("prelude.apex");
        let module = apex_syntax::parse(src).expect("prelude must parse");
        el.elab_module(&module).unwrap_or_else(|e| {
            let (line, _) = e.span.line_col(src);
            panic!(
                "prelude must elaborate: {} (prelude.apex line {line})",
                e.msg
            )
        });
        el.prelude_loaded = true;
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
            ItemKind::Trait(t) => self.elab_trait(t, item.span),
            ItemKind::Impl(i) => self.elab_impl(i, item.span),
        }
    }

    fn cx(&self) -> Cx<'_> {
        Cx::new(&self.env, &self.masks, &self.aliases, &self.tables)
    }

    fn add_def(&mut self, name: &Ident, ty: T, val: T, mask: Vec<Bk>) -> R<()> {
        // a user definition may shadow a prelude one; it then lives under another kernel name
        let mut kname = name.name.clone();
        if self.prelude_loaded {
            if self.user_defs.contains(&name.name) {
                return err(name.span, format!("`{}` is already declared", name.name));
            }
            if self.env.get(&name.name).is_some() {
                kname = format!("{}'user", name.name);
                self.tables.shadow.insert(name.name.clone(), kname.clone());
            }
            self.user_defs.insert(name.name.clone());
        }
        from_kernel(self.env.add_def(&kname, &[], ty, val), name.span)?;
        self.masks.insert(kname, mask);
        Ok(())
    }

    fn elab_fn(&mut self, f: &FnDecl, span: Span) -> R<()> {
        let recursive = f
            .body
            .as_ref()
            .is_some_and(|b| mentions_block(b, &f.name.name));
        let (ty, val, mask) = if !recursive {
            self.try_fn(f, span, None, None)?
        } else {
            // structural recursion: try each parameter as the decreasing one
            let mut first_err = None;
            let mut found = None;
            for k in 0..f.params.len() {
                match self.try_fn(f, span, Some(k), None) {
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
    fn try_fn(
        &self,
        f: &FnDecl,
        span: Span,
        decr: Option<usize>,
        self_ty: Option<&Expr>,
    ) -> R<(T, T, Vec<Bk>)> {
        let mut cx = self.cx();
        let (mut fvs, mut mask) = cx.elab_binders(&f.generics, &[])?;
        if let Some(e) = self_ty {
            let t = cx.elab_type(e)?;
            cx.scope.push(("Self".into(), t));
        }
        let (pf, pm) = cx.elab_binders(&[], &f.params)?;
        fvs.extend(pf);
        mask.extend(pm);
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
                refined: Vec::new(),
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

    /// The type of an inductive type former: `Π params, Sort level`.
    fn ind_type(&self, generics: &[Generic], level: u32, span: Span) -> R<T> {
        let mut cx = self.cx();
        let (pfv, _) = cx.elab_binders(generics, &[])?;
        let declared = generics
            .iter()
            .filter(|g| !g.name.name.starts_with('\''))
            .count();
        if pfv.len() != declared {
            return err(
                span,
                "trait bounds on type declarations are not supported yet",
            );
        }
        cx.close(&pfv, &sort(Level::of_nat(level)), true, span)
    }

    fn register_inductive(&mut self, decl: InductiveDecl, nparams: usize, span: Span) -> R<()> {
        let name = decl.name.to_string();
        let ctor_names: Vec<String> = decl.ctors.iter().map(|(n, _)| n.to_string()).collect();
        from_kernel(self.env.add_inductive(decl), span)?;
        for cn in ctor_names {
            // parameters are implicit in constructors
            self.masks.insert(cn.clone(), vec![Bk::Imp; nparams]);
            if let Some(short) = cn.strip_prefix(&format!("{name}.")) {
                if short != "mk"
                    && self.env.get(short).is_none()
                    && !self.aliases.contains_key(short)
                {
                    self.aliases.insert(short.to_string(), cn.clone());
                }
            }
        }
        Ok(())
    }

    fn elab_enum(&mut self, d: &EnumDecl, span: Span) -> R<()> {
        let ind_ty = self.ind_type(&d.generics, 1, span)?;
        let name = d.name.name.clone();
        // scratch environment in which the type is visible, for recursive fields
        let mut scratch = self.env.clone();
        from_kernel(scratch.add_axiom(&name, &[], ind_ty.clone()), d.name.span)?;
        let mut ctors = Vec::new();
        {
            let mut cx = Cx::new(&scratch, &self.masks, &self.aliases, &self.tables);
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
        let ind_ty = self.ind_type(&d.generics, 1, span)?;
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
            let mut cx = Cx::new(&scratch, &self.masks, &self.aliases, &self.tables);
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
            self.add_projection(&name, nparams, j, &field.name, Bk::Exp, &|cx| {
                cx.struct_telescope(d)
            })?;
        }
        Ok(())
    }

    /// `N.f := fun params (s : N params) => N.rec (fun _ => T_f) (fun fields => f) s`.
    /// `last` says how the final binder (the structure or the instance) is supplied.
    fn add_projection(
        &mut self,
        ind: &str,
        nparams: usize,
        j: usize,
        fname: &Ident,
        last: Bk,
        mk_tele: &dyn Fn(&mut Cx<'_>) -> R<StructTele>,
    ) -> R<()> {
        let (ty, val, extra) = {
            let mut cx = self.cx();
            let tele = mk_tele(&mut cx)?;
            let fty = tele.field_tys[j].clone();
            if tele.fields[..j].iter().any(|&f| contains_fvar(&fty, f)) {
                return err(
                    fname.span,
                    "fields that depend on earlier fields are not supported yet",
                );
            }
            let self_ty = mk_apps(&cnst(ind.into(), vec![]), &tele.pargs());
            let s = cx.tc.fresh("self", self_ty.clone(), Mult::Omega);
            let lvl = from_kernel(cx.tc.check_is_type(&fty), fname.span)?;
            let t0 = cx.tc.fresh("t", self_ty, Mult::Omega);
            let motive = cx.tc.mk_lam(&[t0], &fty);
            let minor = cx.tc.mk_lam(&tele.fields, &fvar(tele.fields[j]));
            let rec = cnst(format!("{ind}.rec").as_str().into(), vec![lvl]);
            let mut args = tele.pargs();
            args.extend([motive, minor, fvar(s)]);
            let body = mk_apps(&rec, &args);
            let binders: Vec<u32> = tele.params.iter().copied().chain([s]).collect();
            let extra = tele.field_masks.get(j).cloned().unwrap_or_default();
            (
                cx.close(&binders, &fty, true, fname.span)?,
                cx.close(&binders, &body, false, fname.span)?,
                extra,
            )
        };
        let pname = Ident {
            name: format!("{ind}.{}", fname.name),
            span: fname.span,
        };
        let mut mask = vec![Bk::Imp; nparams];
        mask.push(last);
        mask.extend(extra);
        self.add_def(&pname, ty, val, mask)
    }

    // ---- traits and impls ----

    /// A trait becomes a one-constructor structure (the "dictionary") whose
    /// fields are the methods; each method is a projection that takes the
    /// instance as an instance-implicit argument.
    fn elab_trait(&mut self, d: &TraitDecl, span: Span) -> R<()> {
        let name = d.name.name.clone();
        if self.env.get(&name).is_some() {
            return err(d.name.span, format!("`{name}` is already declared"));
        }
        // a method with its own type parameters makes the field a `Π (B : Type), ..`,
        // which lives one universe higher
        let generic_methods = d
            .fns
            .iter()
            .any(|m| m.generics.iter().any(|g| !g.name.name.starts_with('\'')));
        let level = if generic_methods { 2 } else { 1 };
        let mut gens = vec![Generic {
            name: Ident {
                name: "Self".into(),
                span: d.name.span,
            },
            ty: None,
        }];
        gens.extend(d.generics.iter().cloned());
        let nparams = gens
            .iter()
            .filter(|g| !g.name.name.starts_with('\''))
            .count();
        let ind_ty = self.ind_type(&gens, level, span)?;
        let mut scratch = self.env.clone();
        from_kernel(scratch.add_axiom(&name, &[], ind_ty.clone()), d.name.span)?;
        let ctor_ty = {
            let mut cx = Cx::new(&scratch, &self.masks, &self.aliases, &self.tables);
            let tele = cx.trait_telescope(&gens, d)?;
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
                ctors: vec![(format!("{name}.mk").as_str().into(), ctor_ty)],
            },
            nparams,
            span,
        )?;
        for (j, m) in d.fns.iter().enumerate() {
            self.add_projection(&name, nparams, j, &m.name, Bk::Inst, &|cx| {
                cx.trait_telescope(&gens, d)
            })?;
        }
        let methods: Vec<String> = d.fns.iter().map(|m| m.name.name.clone()).collect();
        for m in &methods {
            self.tables
                .methods
                .entry(m.clone())
                .or_default()
                .push(name.clone());
        }
        let info = TraitInfo {
            nparams,
            methods,
            generics: d
                .generics
                .iter()
                .filter(|g| !g.name.name.starts_with('\''))
                .map(|g| g.name.name.clone())
                .collect(),
            defaults: d
                .fns
                .iter()
                .filter(|m| m.body.is_some())
                .map(|m| (m.name.name.clone(), m.clone()))
                .collect(),
        };
        self.tables.traits.insert(name, info);
        Ok(())
    }

    fn elab_impl(&mut self, d: &ImplDecl, span: Span) -> R<()> {
        match &d.trait_ref {
            Some(tr) => self.elab_trait_impl(d, tr, span),
            None => self.elab_inherent_impl(d, span),
        }
    }

    /// `impl<G> Trait<A> for Ty { fn .. }` becomes a definition
    /// `inst : Π G, Trait Ty A := Trait.mk Ty A (method terms)`.
    ///
    /// Methods are built one at a time; a method may use the ones built before it
    /// (through a provisional dictionary whose unbuilt fields are placeholders).
    /// Methods the impl omits take the trait's default body.
    fn elab_trait_impl(&mut self, d: &ImplDecl, tr: &Expr, span: Span) -> R<()> {
        let (trait_name, ty, val, mask) = {
            let mut cx = self.cx();
            let Some((tname, targs)) = cx.trait_ref(tr) else {
                return err(tr.span, "expected the name of a trait");
            };
            let info = self.tables.traits[&tname].clone();
            let (fvs, mask) = cx.elab_binders(&d.generics, &[])?;
            let self_ty = cx.elab_type(&d.self_ty)?;
            cx.scope.push(("Self".into(), self_ty.clone()));
            let mut class_args = vec![self_ty];
            for a in targs {
                class_args.push(cx.elab_type(a)?);
            }
            if class_args.len() != info.nparams {
                return err(
                    tr.span,
                    format!(
                        "trait `{tname}` takes {} type arguments (`Self` included), but {} were given",
                        info.nparams,
                        class_args.len()
                    ),
                );
            }
            let class_app = mk_apps(&cnst(tname.as_str().into(), vec![]), &class_args);
            let ctor = format!("{tname}.mk");
            let ctor_ty = from_kernel(self.env.const_type(&ctor, &[]), span)?;
            // field types, with placeholders standing for the methods not built yet
            let mut cur = from_kernel(cx.tc.instantiate_pis(&ctor_ty, &class_args), span)?;
            let (mut doms, mut holes) = (Vec::new(), Vec::new());
            for mname in &info.methods {
                let w = from_kernel(cx.tc.whnf(&cur), span)?;
                let Term::Pi(_, dom, body) = &*w else {
                    return err(span, "internal error: malformed trait structure");
                };
                let hole = cx.tc.fresh(&format!("<{mname}>"), dom.clone(), Mult::Omega);
                doms.push(dom.clone());
                holes.push(hole);
                cur = instantiate(body, &fvar(hole));
            }
            if let Some(extra) = d.fns.iter().find(|f| !info.methods.contains(&f.name.name)) {
                return err(
                    extra.name.span,
                    format!("`{}` is not a method of `{tname}`", extra.name.name),
                );
            }
            let n = info.methods.len();
            cx.pending = Some(Pending {
                trait_name: tname.clone(),
                class_args: class_args.clone(),
                built: vec![None; n],
                holes,
                methods: info.methods.clone(),
            });

            // the methods the impl writes, retrying those that need a later sibling
            let mut todo: Vec<usize> = (0..n)
                .filter(|&i| d.fns.iter().any(|f| f.name.name == info.methods[i]))
                .collect();
            while !todo.is_empty() {
                let mut progress = false;
                let mut first_err = None;
                for i in todo.clone() {
                    let f = d
                        .fns
                        .iter()
                        .find(|f| f.name.name == info.methods[i])
                        .expect("present");
                    let (depth, nlocal, ngoals) =
                        (cx.scope.len(), cx.local_insts.len(), cx.goals.len());
                    let snap = cx.tc.snapshot();
                    match cx.elab_method(f, &doms[i]) {
                        Ok(term) => {
                            cx.pending.as_mut().expect("pending").built[i] = Some(term);
                            todo.retain(|&j| j != i);
                            progress = true;
                        }
                        Err(e) if e.msg.contains(NOT_BUILT) => {
                            cx.scope.truncate(depth);
                            cx.local_insts.truncate(nlocal);
                            cx.goals.truncate(ngoals);
                            cx.tc.restore(snap);
                            first_err.get_or_insert(e);
                        }
                        Err(e) => return Err(e),
                    }
                }
                if !progress {
                    return Err(first_err.expect("an error was recorded"));
                }
            }

            // default bodies for the rest; they may name the trait's own parameters
            let depth = cx.scope.len();
            for (g, a) in info.generics.iter().zip(class_args.iter().skip(1)) {
                cx.scope.push((g.clone(), a.clone()));
            }
            for (i, (mname, dom)) in info.methods.iter().zip(&doms).enumerate() {
                if cx.pending.as_ref().expect("pending").built[i].is_some() {
                    continue;
                }
                let Some(f) = info.defaults.get(mname) else {
                    return err(
                        span,
                        format!("missing method `{mname}` in this impl of `{tname}`"),
                    );
                };
                let term = cx.elab_method(f, dom)?;
                cx.pending.as_mut().expect("pending").built[i] = Some(term);
            }
            cx.scope.truncate(depth);

            let terms: Vec<T> = cx
                .pending
                .take()
                .expect("pending")
                .built
                .into_iter()
                .map(|t| t.expect("all methods built"))
                .collect();
            let mut mk_args = class_args;
            mk_args.extend(terms);
            let value = mk_apps(&cnst(ctor.as_str().into(), vec![]), &mk_args);
            let ty = cx.close(&fvs, &class_app, true, span)?;
            let val = cx.close(&fvs, &value, false, span)?;
            (tname, ty, val, mask)
        };
        self.check_overlap(&trait_name, &ty, &mask, span)?;
        self.inst_counter += 1;
        let name = format!("inst_{trait_name}_{}", self.inst_counter);
        self.add_def(
            &Ident {
                name: name.clone(),
                span,
            },
            ty,
            val,
            mask,
        )?;
        self.tables.insts.entry(trait_name).or_default().push(name);
        Ok(())
    }

    /// Two impls of one trait may not apply to the same type.
    fn check_overlap(&self, trait_name: &str, ty: &T, mask: &[Bk], span: Span) -> R<()> {
        let Some(olds) = self.tables.insts.get(trait_name) else {
            return Ok(());
        };
        for old in olds {
            let mut cx = self.cx();
            let (_, r_new, _) = cx.open_binders(cnst("new".into(), vec![]), ty.clone(), mask)?;
            let (_, r_old, _) = cx.open_instance(old)?;
            if from_kernel(cx.tc.is_def_eq(&r_new, &r_old), span)? {
                return err(
                    span,
                    format!("this impl overlaps with an existing impl of `{trait_name}`"),
                );
            }
        }
        Ok(())
    }

    /// `impl Ty { fn m(..) }` defines `Ty.m`, callable as `x.m(..)`.
    fn elab_inherent_impl(&mut self, d: &ImplDecl, span: Span) -> R<()> {
        let head = {
            let mut cx = self.cx();
            cx.elab_binders(&d.generics, &[])?;
            let t = cx.elab_type(&d.self_ty)?;
            let w = from_kernel(cx.tc.whnf(&t), span)?;
            let (h, _) = app_spine(&w);
            match &*h {
                Term::Const(n, _) => n.to_string(),
                _ => {
                    return err(
                        d.self_ty.span,
                        "an impl needs a named type, like a struct or an enum",
                    )
                }
            }
        };
        for f in &d.fns {
            let mut generics = d.generics.clone();
            generics.extend(f.generics.iter().cloned());
            let fd = FnDecl {
                name: Ident {
                    name: format!("{head}.{}", f.name.name),
                    span: f.name.span,
                },
                generics,
                params: f.params.clone(),
                ret: f.ret.clone(),
                body: f.body.clone(),
            };
            let (ty, val, mask) = self.try_fn(&fd, span, None, Some(&d.self_ty))?;
            self.add_def(&fd.name, ty, val, mask)?;
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
    /// A field variable that a nested `match` replaced by a constructor
    /// application, so recursive calls on it can still be recognized.
    refined: Vec<(T, u32)>,
    in_top: bool,
}

struct StructTele {
    params: Vec<u32>,
    fields: Vec<u32>,
    field_tys: Vec<T>,
    /// Binder kinds of each field's own leading generics (trait methods only).
    field_masks: Vec<Vec<Bk>>,
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
    tables: &'a Tables,
    /// Instance arguments waiting for their types to become known.
    goals: Vec<(T, Span)>,
    /// Instance variables in scope (from `T: Trait` bounds).
    local_insts: Vec<T>,
    scope: Vec<(String, T)>,
    rec: Option<RecCtx>,
    pending: Option<Pending>,
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
    fn new(env: &'a Env, masks: &'a Masks, aliases: &'a Aliases, tables: &'a Tables) -> Self {
        Cx {
            tc: TypeChecker::new(env),
            env,
            masks,
            aliases,
            tables,
            goals: Vec::new(),
            local_insts: Vec::new(),
            scope: Vec::new(),
            rec: None,
            pending: None,
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
    fn elab_binders(&mut self, generics: &[Generic], params: &[Param]) -> R<(Vec<u32>, Vec<Bk>)> {
        let mut fvs = Vec::new();
        let mut mask = Vec::new();
        for g in generics {
            if g.name.name.starts_with('\'') {
                continue; // lifetimes are handled by the borrow checker
            }
            let bounds = match &g.ty {
                Some(t) => self.bound_list(t)?,
                None => None,
            };
            let ty = match (&g.ty, &bounds) {
                (Some(t), None) => self.elab_type(t)?,
                _ => sort(Level::of_nat(1)),
            };
            let mult = if self.is_sort(&ty) {
                Mult::Zero
            } else {
                Mult::Omega
            };
            let id = self.tc.fresh(&g.name.name, ty, mult);
            self.scope.push((g.name.name.clone(), fvar(id)));
            fvs.push(id);
            mask.push(Bk::Imp);
            // `T: Trait` adds a dictionary parameter, found by instance search at call sites
            for (tn, targs) in bounds.into_iter().flatten() {
                let mut cargs = vec![fvar(id)];
                for a in targs {
                    cargs.push(self.elab_type(a)?);
                }
                let cty = mk_apps(&cnst(tn.as_str().into(), vec![]), &cargs);
                let d = self.tc.fresh("inst", cty, Mult::Omega);
                fvs.push(d);
                mask.push(Bk::Inst);
                self.local_insts.push(fvar(d));
            }
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
            mask.push(Bk::Exp);
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
            field_masks: vec![],
        })
    }

    /// Zonk and abstract `fvs` over `body`; fails if metavariables remain.
    fn close(&mut self, fvs: &[u32], body: &T, is_pi: bool, span: Span) -> R<T> {
        self.solve_goals(true)?;
        self.tc.zonk_locals();
        let body = self.tc.zonk(body);
        let body = self.devirt(&body);
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
        if let Some(k) = self.tables.shadow.get(name) {
            return Some(Res::Global(k.clone()));
        }
        if self.env.get(name).is_some() {
            return Some(Res::Global(name.to_string()));
        }
        self.aliases.get(name).map(|full| Res::Global(full.clone()))
    }

    /// A constant applied to fresh universe level metavariables.
    fn const_term(&mut self, name: &str) -> (T, Vec<Bk>) {
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

    fn head_of(&mut self, path: &str) -> Option<(T, Vec<Bk>)> {
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
                // `a + b` is `Add.add(a, b)`, and so on
                let (name, swap) = match op {
                    BinOp::Eq => ("Eq", false),
                    BinOp::Add => ("Add.add", false),
                    BinOp::Sub => ("Sub.sub", false),
                    BinOp::Mul => ("Mul.mul", false),
                    BinOp::EqEq => ("BEq.beq", false),
                    BinOp::Lt => ("Ord.lt", false),
                    BinOp::Gt => ("Ord.lt", true),
                    BinOp::Div => ("Div.div", false),
                    BinOp::Rem => ("Rem.rem", false),
                };
                let head = self.const_term(name);
                let args = if swap {
                    vec![Arg::Expr(r), Arg::Expr(l)]
                } else {
                    vec![Arg::Expr(l), Arg::Expr(r)]
                };
                self.elab_app(head, args, exp, e.span)
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
                        let ExprKind::Field(base, m) = &f.kind else {
                            unreachable!()
                        };
                        return self.elab_method_call(base, m, args, exp, e.span);
                    }
                    None => (self.elab(f, None)?, vec![]),
                };
                self.elab_app(head, args.iter().map(Arg::Expr).collect(), exp, e.span)
            }
            ExprKind::Block(b) => self.elab_block(b, exp),
            ExprKind::Do(b) => self.elab_do(b, exp, e.span),
            ExprKind::For { var, iter, body } => self.elab_for(var, iter, body, e.span),
            ExprKind::Lambda { params, body } => self.elab_lambda(params, body, exp, e.span),
            ExprKind::List(items) => {
                // [a, b] is List.cons(a, List.cons(b, List.nil))
                let var = |n: &str, span| Expr {
                    kind: ExprKind::Var(n.into()),
                    span,
                };
                let mut list = var("List.nil", e.span);
                for it in items.iter().rev() {
                    list = Expr {
                        kind: ExprKind::Call(
                            Box::new(var("List.cons", it.span)),
                            vec![it.clone(), list],
                        ),
                        span: e.span,
                    };
                }
                self.elab(&list, exp)
            }
            ExprKind::If(cond, then, els) => self.elab_if(cond, then, els.as_deref(), exp, e.span),
            // references are not tracked yet: `&x` elaborates as `x` (the borrow checker is M5)
            ExprKind::Ref { inner, .. } => self.elab(inner, exp),
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
        head: (T, Vec<Bk>),
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
                    let kind = mask.get(i).copied().unwrap_or(Bk::Exp);
                    if kind == Bk::Exp && next >= args.len() {
                        break;
                    }
                    let mv = self.new_mvar(d.clone(), span);
                    term = app(term, mv.clone());
                    fty = instantiate(b, &mv);
                    i += 1;
                    match kind {
                        Bk::Exp => {
                            pending.push((mv, next));
                            next += 1;
                        }
                        Bk::Imp => {}
                        Bk::Inst => self.goals.push((mv, span)),
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
        self.solve_goals(false)?;
        Ok(term)
    }

    // ---- traits: bounds, instance search, methods ----

    /// `Trait` or `Trait<A, ..>` naming a declared trait.
    fn trait_ref<'e>(&self, e: &'e Expr) -> Option<(String, &'e [Expr])> {
        let (head, args): (&Expr, &[Expr]) = match &e.kind {
            ExprKind::TypeApp(f, args) | ExprKind::Call(f, args) => (f, args.as_slice()),
            _ => (e, &[]),
        };
        let p = path_name(head)?;
        if self.scope.iter().any(|(n, _)| *n == p) {
            return None; // a variable shadows the trait name
        }
        self.tables.traits.contains_key(&p).then_some((p, args))
    }

    /// The traits in a bound like `Show + Eq`, or `None` if `e` is an ordinary
    /// type annotation.
    fn bound_list<'e>(&self, e: &'e Expr) -> R<Option<Vec<Bound<'e>>>> {
        let mut parts = Vec::new();
        flatten_add(e, &mut parts);
        let refs: Vec<_> = parts.iter().map(|p| self.trait_ref(p)).collect();
        if refs.iter().all(Option::is_none) {
            return Ok(None);
        }
        if refs.iter().any(Option::is_none) {
            return err(e.span, "a bound may only mention traits");
        }
        Ok(Some(refs.into_iter().flatten().collect()))
    }

    fn trait_telescope(&mut self, gens: &[Generic], d: &TraitDecl) -> R<StructTele> {
        let (params, _) = self.elab_binders(gens, &[])?;
        let mut fields = Vec::new();
        let mut field_tys = Vec::new();
        let mut field_masks = Vec::new();
        for m in &d.fns {
            let (depth, nlocal) = (self.scope.len(), self.local_insts.len());
            let (pf, mask) = self.elab_binders(&m.generics, &m.params)?;
            let ret = match &m.ret {
                Some(t) => self.elab_type(t)?,
                None => self.unit_type(),
            };
            let fty = self.close(&pf, &ret, true, m.name.span)?;
            self.scope.truncate(depth);
            self.local_insts.truncate(nlocal);
            let id = self.tc.fresh(&m.name.name, fty.clone(), Mult::Omega);
            fields.push(id);
            field_tys.push(fty);
            field_masks.push(mask);
        }
        Ok(StructTele {
            params,
            fields,
            field_tys,
            field_masks,
        })
    }

    /// Elaborate an impl method as a term of type `expected`.
    fn elab_method(&mut self, f: &FnDecl, expected: &T) -> R<T> {
        let Some(block) = &f.body else {
            return err(f.name.span, "a method in an impl needs a body");
        };
        let (depth, nlocal) = (self.scope.len(), self.local_insts.len());
        let (pf, _) = self.elab_binders(&f.generics, &f.params)?;
        let ret = match &f.ret {
            Some(t) => self.elab_type(t)?,
            None => self.unit_type(),
        };
        let body = self.elab_block(block, Some(&ret))?;
        let body = self.coerce(body, &ret, block.span)?;
        let ty = self.close(&pf, &ret, true, f.name.span)?;
        if !from_kernel(self.tc.is_def_eq(&ty, expected), f.name.span)? {
            return err(
                f.name.span,
                format!(
                    "method `{}` has type `{}`, but the trait requires `{}`",
                    f.name.name,
                    self.pp(&ty),
                    self.pp(expected)
                ),
            );
        }
        let term = self.close(&pf, &body, false, f.name.span)?;
        self.scope.truncate(depth);
        self.local_insts.truncate(nlocal);
        // placeholders must not survive: they stand for methods not built yet
        if let Some(p) = &self.pending {
            for (j, &h) in p.holes.iter().enumerate() {
                if contains_fvar(&term, h) {
                    return err(
                        f.name.span,
                        format!(
                            "method `{}` of this impl {NOT_BUILT} (an impl cannot refer to itself as a whole)",
                            p.methods[j]
                        ),
                    );
                }
            }
        }
        Ok(term)
    }

    /// Open the leading binders of `fty` (a constant applied to `term` so far)
    /// as metavariables, returning the instance-binder metavariables separately.
    fn open_binders(&mut self, mut term: T, mut fty: T, mask: &[Bk]) -> R<(T, T, Vec<T>)> {
        let mut subgoals = Vec::new();
        let mut i = 0;
        loop {
            let w = from_kernel(self.tc.whnf(&fty), Span::default())?;
            let Term::Pi(_, d, b) = &*w else {
                return Ok((term, w, subgoals));
            };
            if i >= mask.len() {
                return Ok((term, w.clone(), subgoals));
            }
            let mv = self.new_mvar(d.clone(), Span::default());
            if mask[i] == Bk::Inst {
                subgoals.push(mv.clone());
            }
            term = app(term, mv.clone());
            fty = instantiate(b, &mv);
            i += 1;
        }
    }

    fn open_instance(&mut self, name: &str) -> R<(T, T, Vec<T>)> {
        let (t, mask) = self.const_term(name);
        let fty = from_kernel(self.tc.infer(&t), Span::default())?;
        self.open_binders(t, fty, &mask)
    }

    fn class_of(&self, ty: &T) -> Option<String> {
        let (h, _) = app_spine(&self.tc.zonk(ty));
        match &*h {
            Term::Const(n, _) if self.tables.traits.contains_key(&**n) => Some(n.to_string()),
            _ => None,
        }
    }

    /// Find an instance for the class application `goal`: first the bounds in
    /// scope, then declared impls (whose own bounds become subgoals).
    fn synth(&mut self, goal: &T, depth: usize, span: Span) -> R<Option<T>> {
        if depth > 12 {
            return Ok(None);
        }
        let g = self.tc.zonk(goal);
        let Some(class) = self.class_of(&g) else {
            return Ok(None);
        };
        // the impl being built: a dictionary of the methods built so far
        if let Some(p) = &self.pending {
            if p.trait_name == class {
                let class_app = mk_apps(&cnst(class.as_str().into(), vec![]), &p.class_args);
                let fields: Vec<T> = p
                    .built
                    .iter()
                    .zip(&p.holes)
                    .map(|(b, &h)| b.clone().unwrap_or_else(|| fvar(h)))
                    .collect();
                let mut args = p.class_args.clone();
                args.extend(fields);
                let dict = mk_apps(&cnst(format!("{class}.mk").as_str().into(), vec![]), &args);
                let snap = self.tc.snapshot();
                if from_kernel(self.tc.is_def_eq(&class_app, &g), span)? {
                    return Ok(Some(dict));
                }
                self.tc.restore(snap);
            }
        }
        for li in self.local_insts.clone() {
            let lty = from_kernel(self.tc.infer(&li), span)?;
            let snap = self.tc.snapshot();
            if from_kernel(self.tc.is_def_eq(&lty, &g), span)? {
                return Ok(Some(li));
            }
            self.tc.restore(snap);
        }
        let names = self.tables.insts.get(&class).cloned().unwrap_or_default();
        for name in names {
            let snap = self.tc.snapshot();
            let (term, res, subgoals) = self.open_instance(&name)?;
            if !from_kernel(self.tc.is_def_eq(&res, &g), span)? {
                self.tc.restore(snap);
                continue;
            }
            let mut ok = true;
            for sg in subgoals {
                let dom = from_kernel(self.tc.infer(&sg), span)?;
                match self.synth(&dom, depth + 1, span)? {
                    Some(t) if from_kernel(self.tc.is_def_eq(&sg, &t), span)? => {}
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                return Ok(Some(term));
            }
            self.tc.restore(snap);
        }
        Ok(None)
    }

    /// Resolve pending instance arguments. A goal whose type still has
    /// metavariables is postponed unless `force` is set.
    fn solve_goals(&mut self, force: bool) -> R<()> {
        loop {
            let goals = std::mem::take(&mut self.goals);
            if goals.is_empty() {
                return Ok(());
            }
            let mut rest = Vec::new();
            let mut progress = false;
            for (mv, span) in goals {
                if !matches!(&*self.tc.zonk(&mv), Term::MVar(_)) {
                    continue; // already solved by unification
                }
                let ty = from_kernel(self.tc.infer(&mv), span)?;
                let ty = self.tc.zonk(&ty);
                let stuck = first_mvar(&ty).is_some();
                // Like Rust, never pick an impl to *determine* a type: a goal whose
                // type is still unknown stays pending, and is an error at the end.
                if stuck {
                    rest.push((mv, span));
                    continue;
                }
                match self.synth(&ty, 0, span)? {
                    Some(t) => {
                        from_kernel(self.tc.is_def_eq(&mv, &t), span)?;
                        progress = true;
                    }
                    None if stuck => rest.push((mv, span)),
                    None => {
                        return err(
                            span,
                            format!("no implementation of `{}` was found", self.pp(&ty)),
                        )
                    }
                }
            }
            let done = rest.is_empty();
            self.goals = rest;
            if done || !progress {
                if force && !self.goals.is_empty() {
                    let (mv, span) = self.goals[0].clone();
                    let ty = from_kernel(self.tc.infer(&mv), span)?;
                    return err(
                        span,
                        format!(
                            "cannot tell which implementation of `{}` to use; add a type annotation",
                            self.pp(&ty)
                        ),
                    );
                }
                return Ok(());
            }
        }
    }

    fn method_args<'e>(base: &T, args: &'e [Expr]) -> Vec<Arg<'e>> {
        std::iter::once(Arg::Term(base.clone()))
            .chain(args.iter().map(Arg::Expr))
            .collect()
    }

    /// `base.m(args)`: an inherent method or projection `Ty.m`, or a trait method.
    fn elab_method_call(
        &mut self,
        base: &Expr,
        m: &Ident,
        args: &[Expr],
        exp: Option<&T>,
        span: Span,
    ) -> R<T> {
        let b = self.elab(base, None)?;
        let b = self.tc.zonk(&b);
        let bt = from_kernel(self.tc.infer(&b), base.span)?;
        let bt = self.tc.zonk(&bt);
        let bt = from_kernel(self.tc.whnf(&bt), base.span)?;
        // `T.method(args)` with `T` a type: a trait method with `Self := T`
        if matches!(&*bt, Term::Sort(_)) {
            let traits = self
                .tables
                .methods
                .get(&m.name)
                .cloned()
                .unwrap_or_default();
            let Some(tn) = traits.first() else {
                return err(m.span, format!("no method `{}` found", m.name));
            };
            let (head, mask) = self.const_term(&format!("{tn}.{}", m.name));
            let mask = mask.get(1..).map(<[Bk]>::to_vec).unwrap_or_default();
            let call_args: Vec<Arg> = args.iter().map(Arg::Expr).collect();
            return self.elab_app((app(head, b), mask), call_args, exp, span);
        }
        let (h, _) = app_spine(&bt);
        if let Term::Const(tn, _) = &*h {
            let inherent = format!("{tn}.{}", m.name);
            if matches!(self.env.get(&inherent), Some(Decl::Def { .. })) {
                let head = self.const_term(&inherent);
                return self.elab_app(head, Self::method_args(&b, args), exp, span);
            }
        }
        let traits = self
            .tables
            .methods
            .get(&m.name)
            .cloned()
            .unwrap_or_default();
        if traits.is_empty() {
            return err(
                m.span,
                format!("no method `{}` found for type `{}`", m.name, self.pp(&bt)),
            );
        }
        let mut first_err = None;
        for tn in &traits {
            let head = self.const_term(&format!("{tn}.{}", m.name));
            if traits.len() == 1 {
                return self.elab_app(head, Self::method_args(&b, args), exp, span);
            }
            let (snap, ngoals) = (self.tc.snapshot(), self.goals.len());
            match self.elab_app(head, Self::method_args(&b, args), exp, span) {
                Ok(t) => return Ok(t),
                Err(e) => {
                    self.tc.restore(snap);
                    self.goals.truncate(ngoals);
                    first_err.get_or_insert(e);
                }
            }
        }
        Err(first_err.expect("at least one candidate trait"))
    }

    /// Replace `Trait.method Ty inst` by the method's body when `inst` is a
    /// closed instance, so statically known calls do not pay for the dictionary.
    fn devirt(&mut self, t: &T) -> T {
        match &**t {
            Term::App(..) => {
                let (f, args) = app_spine(t);
                let args: Vec<T> = args.iter().map(|a| self.devirt(a)).collect();
                if let Term::Const(n, _) = &*f {
                    if let Some((tn, mn)) = n.split_once('.') {
                        let nparams =
                            self.tables.traits.get(tn).and_then(|i| {
                                i.methods.iter().any(|m| m == mn).then_some(i.nparams)
                            });
                        if let Some(np) = nparams {
                            let mk = format!("{tn}.mk");
                            let is_mk = args.len() > np
                                && matches!(&*app_spine(&args[np]).0, Term::Const(c, _) if **c == *mk);
                            if args.len() > np
                                && args[..=np].iter().all(|a| !has_bvar(a))
                                && (is_mk || !has_fvar(&args[np]))
                                && first_mvar(&args[np]).is_none()
                            {
                                let head = mk_apps(&f, &args[..=np]);
                                if let Ok(r) = self.tc.whnf(&head) {
                                    if r != head {
                                        let again = head_beta(&mk_apps(&r, &args[np + 1..]));
                                        return self.devirt(&again);
                                    }
                                }
                            }
                        }
                    }
                }
                mk_apps(&self.devirt(&f), &args)
            }
            Term::Lam(m, ty, b) => lam(*m, self.devirt(ty), self.devirt(b)),
            Term::Pi(m, ty, b) => pi(*m, self.devirt(ty), self.devirt(b)),
            Term::Let(m, ty, v, b) => let_(*m, self.devirt(ty), self.devirt(v), self.devirt(b)),
            _ => t.clone(),
        }
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

    /// `|x, y| body`: parameter types come from the expected function type
    /// unless annotated.
    fn elab_lambda(
        &mut self,
        params: &[LamParam],
        body: &Expr,
        exp: Option<&T>,
        span: Span,
    ) -> R<T> {
        let (depth, nlocal) = (self.scope.len(), self.local_insts.len());
        let mut xs = Vec::new();
        let mut expected = exp.cloned();
        for p in params {
            let from_exp = match &expected {
                Some(t) => {
                    let t = self.tc.zonk(t);
                    let w = from_kernel(self.tc.whnf(&t), p.name.span)?;
                    match &*w {
                        Term::Pi(m, d, b) => Some((*m, d.clone(), b.clone())),
                        _ => None,
                    }
                }
                None => None,
            };
            let ty = match (&p.ty, &from_exp) {
                (Some(t), _) => self.elab_type(t)?,
                (None, Some((_, d, _))) => d.clone(),
                (None, None) => {
                    return err(
                        p.name.span,
                        "cannot infer the type of this closure parameter; add an annotation like `|x: Nat|`",
                    )
                }
            };
            let mult = from_exp.as_ref().map_or(Mult::Omega, |(m, _, _)| *m);
            if let Some((_, d, _)) = &from_exp {
                self.coerce_eq(&ty, d, p.name.span)?;
            }
            let x = self.tc.fresh(&p.name.name, ty, mult);
            self.scope.push((p.name.name.clone(), fvar(x)));
            xs.push(x);
            expected = from_exp.map(|(_, _, b)| instantiate(&b, &fvar(x)));
        }
        let b = match &expected {
            Some(t) => self.elab_check(body, t),
            None => self.elab(body, None),
        };
        self.scope.truncate(depth);
        self.local_insts.truncate(nlocal);
        let b = b?;
        let _ = span;
        self.tc.zonk_locals();
        let b = self.tc.zonk(&b);
        Ok(self.tc.mk_lam(&xs, &b))
    }

    /// `for x in xs { body }` is `for_each(xs, fun x => do { body })`.
    fn elab_for(&mut self, var: &Ident, iter: &Expr, body: &Block, span: Span) -> R<T> {
        let it = self.elab(iter, None)?;
        let it = self.tc.zonk(&it);
        let ity = from_kernel(self.tc.infer(&it), iter.span)?;
        let ity = self.tc.zonk(&ity);
        let ity = from_kernel(self.tc.whnf(&ity), iter.span)?;
        let elem = match &*ity {
            Term::App(f, a) if matches!(&**f, Term::Const(n, _) if &**n == "List") => a.clone(),
            _ => {
                return err(
                    iter.span,
                    format!(
                        "`for` loops iterate over a `List`, but this has type `{}`",
                        self.pp(&ity)
                    ),
                )
            }
        };
        let x = self.tc.fresh(&var.name, elem.clone(), Mult::Omega);
        self.scope.push((var.name.clone(), fvar(x)));
        let unit_io = self.io_type(&self.unit_type());
        let b = self.elab_do(body, Some(&unit_io), span);
        self.scope.pop();
        let lam = self.close_lam(x, &b?);
        Ok(mk_apps(&cnst("for_each".into(), vec![]), &[elem, it, lam]))
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
            if let Some(rc) = &mut self.rec {
                rc.refined.push((ctor_app.clone(), x));
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
        let ih = self.rec.as_ref().and_then(|rc| match &*arg {
            Term::FVar(f) => rc.fields.get(f).cloned(),
            _ => rc
                .refined
                .iter()
                .find(|(t, _)| self.tc.zonk(t) == arg)
                .and_then(|(_, x)| rc.fields.get(x).cloned()),
        });
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
        ExprKind::List(items) => items.iter().any(|a| mentions_expr(a, name)),
        ExprKind::Lambda { body, .. } => mentions_expr(body, name),
        ExprKind::For { iter, body, .. } => mentions_expr(iter, name) || mentions_block(body, name),
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

fn flatten_add<'e>(e: &'e Expr, out: &mut Vec<&'e Expr>) {
    match &e.kind {
        ExprKind::Binary(BinOp::Add, a, b) => {
            flatten_add(a, out);
            flatten_add(b, out);
        }
        _ => out.push(e),
    }
}
