//! The everyday tactics around the core ones: `subst`, `rcases`/`obtain`/`rintro`,
//! `by_cases`, `by_contra`, `specialize`, `refine`, `funext`, `congr`, `calc`, `trivial`.

use super::*;

fn collect_mvars(t: &T, out: &mut Vec<u32>) {
    match &**t {
        Term::MVar(i) => {
            if !out.contains(i) {
                out.push(*i)
            }
        }
        Term::App(f, a) => {
            collect_mvars(f, out);
            collect_mvars(a, out);
        }
        Term::Lam(_, ty, b) | Term::Pi(_, ty, b) => {
            collect_mvars(ty, out);
            collect_mvars(b, out);
        }
        Term::Let(_, ty, v, b) => {
            collect_mvars(ty, out);
            collect_mvars(v, out);
            collect_mvars(b, out);
        }
        _ => {}
    }
}

/// The relation of a `calc` step.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Rel {
    Eq,
    Le,
    Lt,
}

struct Chain {
    rel: Rel,
    level: Level,
    alpha: T,
    lhs: T,
    rhs: T,
    proof: T,
}

fn ident(name: &str, span: Span) -> Ident {
    Ident {
        name: name.to_string(),
        span,
    }
}

impl<'a> Cx<'a> {
    fn hyp_id(&self, g: &Goal, name: &str) -> Option<u32> {
        match g.scope.iter().rfind(|(n, _)| plain_name(n) == name) {
            Some((_, v)) => match &**v {
                Term::FVar(id) => Some(*id),
                _ => None,
            },
            None => None,
        }
    }

    // ---- generalize / cases on an expression ----

    /// Replace the term `e : ty` in the goal by a new variable `x`, with `h : e = x`.
    pub(super) fn generalize_term(
        &mut self,
        st: &mut Tac,
        g: &Goal,
        h: Option<&Ident>,
        (e, ty): (T, T),
        x: &str,
        span: Span,
    ) -> R<(Goal, u32)> {
        let e = self.tc.zonk(&e);
        let tgt = self.tc.zonk(&g.target);
        let abs = replace_term(&tgt, &e, 0);
        let l = self.sort_level_of(&ty, span)?;
        let xv = self.tc.fresh(x, ty.clone(), Mult::Omega);
        let eq = mk_apps(
            &cnst("Eq".into(), vec![l.clone()]),
            &[ty.clone(), e.clone(), fvar(xv)],
        );
        let hn = h.map_or("heq".to_string(), |h| h.name.clone());
        let hv = self.tc.fresh(&hn, eq, Mult::Omega);
        let new_tgt = instantiate(&abs, &fvar(xv));
        let mut ng = self.new_goal(g, new_tgt.clone(), "");
        ng.scope.push((x.to_string(), fvar(xv)));
        ng.scope.push((hn, fvar(hv)));
        let lam_ty = self.tc.mk_pi(&[xv, hv], &new_tgt);
        let lam_mv = self.tc.new_mvar(lam_ty);
        st.sol
            .insert(mvar_id(&lam_mv), Sol::Lam(vec![xv, hv], ng.mv));
        let refl = mk_apps(&cnst("Eq.refl".into(), vec![l]), &[ty, e.clone()]);
        self.solve(st, g, mk_apps(&lam_mv, &[e, refl]));
        Ok((ng, xv))
    }

    /// `cases h : e`: generalize `e`, then split on the new variable.
    pub(super) fn t_cases_eq(
        &mut self,
        st: &mut Tac,
        g: Goal,
        h: &Ident,
        term: (T, T),
        arms: Option<&[CaseArm]>,
        span: Span,
    ) -> R<Vec<Goal>> {
        let (ng, _) = self.generalize_term(st, &g, Some(h), term, "_cv", span)?;
        self.t_induct(st, ng, &ident("_cv", span), &[], arms, false, span)
    }

    // ---- subst ----

    pub(super) fn t_subst(
        &mut self,
        st: &mut Tac,
        g: Goal,
        name: &Ident,
        span: Span,
    ) -> R<Vec<Goal>> {
        let Some(id) = self.hyp_id(&g, &name.name) else {
            return err(name.span, format!("unknown hypothesis `{}`", name.name));
        };
        let ty = from_kernel(self.tc.local_ty(id), span)?;
        let ty = self.tc.zonk(&ty);
        if self.eq_parts(&ty).is_some() {
            return self.subst_eq(st, g, &name.name, id, span);
        }
        // a variable: find an equation that mentions it as one side
        let scope = g.scope.clone();
        for (n, v) in scope.iter().rev() {
            let Term::FVar(hid) = &**v else { continue };
            let Ok(hty) = self.tc.local_ty(*hid) else {
                continue;
            };
            let hty = self.tc.zonk(&hty);
            if let Some((_, _, a, b)) = self.eq_parts(&hty) {
                let (a, b) = (self.tc.zonk(&a), self.tc.zonk(&b));
                let is_x = |t: &T| matches!(&**t, Term::FVar(i) if *i == id);
                if (is_x(&a) && !contains_fvar(&b, id)) || (is_x(&b) && !contains_fvar(&a, id)) {
                    let hn = plain_name(n).to_string();
                    return self.subst_eq(st, g, &hn, *hid, span);
                }
            }
        }
        err(
            name.span,
            format!("`subst`: no equation mentions `{}`", name.name),
        )
    }

    fn subst_eq(
        &mut self,
        st: &mut Tac,
        g: Goal,
        hname: &str,
        hid: u32,
        span: Span,
    ) -> R<Vec<Goal>> {
        let hty = from_kernel(self.tc.local_ty(hid), span)?;
        let Some((l, alpha, a, b)) = self.eq_parts(&hty) else {
            return err(span, "`subst` needs an equation");
        };
        let (a, b) = (self.tc.zonk(&a), self.tc.zonk(&b));
        let is_var = |t: &T, other: &T| match &**t {
            Term::FVar(i) => !contains_fvar(other, *i),
            _ => false,
        };
        if is_var(&b, &a) {
            return self.t_induct(st, g, &ident(hname, span), &[], None, false, span);
        }
        if is_var(&a, &b) {
            let sym = mk_apps(
                &cnst("Eq.symm".into(), vec![l.clone()]),
                &[alpha.clone(), a.clone(), b.clone(), fvar(hid)],
            );
            let sty = mk_apps(&cnst("Eq".into(), vec![l]), &[alpha, b, a]);
            let ng = self.add_hyp(st, &g, "_subst", sty, sym);
            return self.t_induct(st, ng, &ident("_subst", span), &[], None, false, span);
        }
        err(
            span,
            "`subst`: one side of the equation must be a variable that the other side does not mention",
        )
    }

    // ---- rcases ----

    pub(super) fn t_rcases(
        &mut self,
        st: &mut Tac,
        g: Goal,
        e: &Expr,
        pat: &RPat,
        span: Span,
    ) -> R<Vec<Goal>> {
        // the hypothesis to destructure: a name in scope, or a proof term made one
        let (g, hname) = match &e.kind {
            ExprKind::Var(n) if self.hyp_id(&g, n).is_some() => (g, n.clone()),
            _ => {
                let pf = self.elab_in_goal(e, None)?;
                let ty = from_kernel(self.tc.infer(&pf), e.span)?;
                let ty = self.tc.zonk(&ty);
                let ng = self.add_hyp(st, &g, "_rc", ty, pf);
                (ng, "_rc".to_string())
            }
        };
        self.rpat(st, g, &hname, pat, span)
    }

    pub(super) fn t_rintro(
        &mut self,
        st: &mut Tac,
        g: Goal,
        pats: &[RPat],
        span: Span,
    ) -> R<Vec<Goal>> {
        let mut goals = vec![g];
        for (k, p) in pats.iter().enumerate() {
            let tmp = match p {
                RPat::Name(n) if n != "rfl" => n.clone(),
                _ => format!("_ri{k}"),
            };
            let mut next = Vec::new();
            for g in goals {
                let gs = self.t_intro(st, g, &[ident(&tmp, span)], span)?;
                for g2 in gs {
                    if matches!(p, RPat::Name(n) if *n == tmp) {
                        next.push(g2);
                    } else {
                        next.extend(self.rpat(st, g2, &tmp, p, span)?);
                    }
                }
            }
            goals = next;
        }
        Ok(goals)
    }

    /// Destructure the hypothesis `hname` of goal `g` by `pat`.
    pub(super) fn rpat(
        &mut self,
        st: &mut Tac,
        mut g: Goal,
        hname: &str,
        pat: &RPat,
        span: Span,
    ) -> R<Vec<Goal>> {
        match pat {
            RPat::Wild => Ok(vec![g]),
            RPat::Name(n) if n == "rfl" => self.t_subst(st, g, &ident(hname, span), span),
            RPat::Name(n) => {
                if n != hname {
                    if let Some(id) = self.hyp_id(&g, hname) {
                        g.scope.push((n.clone(), fvar(id)));
                    }
                }
                Ok(vec![g])
            }
            RPat::Tuple(_) | RPat::Alt(_) => {
                let Some(id) = self.hyp_id(&g, hname) else {
                    return err(span, format!("unknown hypothesis `{hname}`"));
                };
                let ty = from_kernel(self.tc.local_ty(id), span)?;
                let ty = self.tc.zonk(&ty);
                let w = from_kernel(self.tc.whnf(&ty), span)?;
                let (h, _) = app_spine(&w);
                let ctors: Vec<(String, usize)> = match &*h {
                    Term::Const(n, _) => match self.env.get(n) {
                        Some(Decl::Inductive(info)) => info
                            .ctors
                            .iter()
                            .map(|c| {
                                let nf = match self.env.get(c) {
                                    Some(Decl::Ctor(ci)) => ci.nfields,
                                    _ => 0,
                                };
                                (short(c).to_string(), nf)
                            })
                            .collect(),
                        _ => vec![],
                    },
                    _ => vec![],
                };
                if ctors.is_empty() {
                    return err(
                        span,
                        format!("cannot destructure `{hname}`: its type is not inductive"),
                    );
                }
                // one sub-pattern list per constructor
                let per_ctor: Vec<Vec<RPat>> = match pat {
                    RPat::Tuple(ps) => {
                        if ctors.len() != 1 {
                            return err(
                                span,
                                format!("a tuple pattern needs a one-constructor type, `{hname}` has {}", ctors.len()),
                            );
                        }
                        vec![Self::fit_fields(ps, ctors[0].1)]
                    }
                    RPat::Alt(ps) => {
                        if ps.len() != ctors.len() {
                            return err(
                                span,
                                format!(
                                    "the alternatives must match the {} constructors of the type",
                                    ctors.len()
                                ),
                            );
                        }
                        ps.iter()
                            .zip(&ctors)
                            .map(|(p, (_, nf))| match p {
                                RPat::Tuple(qs) if *nf != 1 || qs.len() == 1 => {
                                    Self::fit_fields(qs, *nf)
                                }
                                other => Self::fit_fields(std::slice::from_ref(other), *nf),
                            })
                            .collect()
                    }
                    _ => unreachable!("matched above"),
                };
                // name the fields after the sub-patterns that are plain names
                let mut names: HashMap<String, Vec<String>> = HashMap::new();
                let tag = g.scope.len();
                for ((cn, nf), subs) in ctors.iter().zip(&per_ctor) {
                    let ns: Vec<String> = (0..*nf)
                        .map(|i| match subs.get(i) {
                            Some(RPat::Name(n)) if n != "rfl" => n.clone(),
                            _ => format!("_rf{tag}_{i}"),
                        })
                        .collect();
                    names.insert(cn.clone(), ns);
                }
                let saved = self.case_names.replace(names.clone());
                let goals = self.t_induct(st, g, &ident(hname, span), &[], None, false, span);
                self.case_names = saved;
                let goals = goals?;
                if goals.len() != ctors.len() {
                    return err(span, "destructuring produced an unexpected number of goals");
                }
                let mut out = Vec::new();
                for ((goal, (cn, _)), subs) in goals.into_iter().zip(&ctors).zip(&per_ctor) {
                    let fnames = &names[cn];
                    let mut cur = vec![goal];
                    for (i, sp) in subs.iter().enumerate() {
                        let mut next = Vec::new();
                        for gg in cur {
                            next.extend(self.rpat(st, gg, &fnames[i], sp, span)?);
                        }
                        cur = next;
                    }
                    out.extend(cur);
                }
                Ok(out)
            }
        }
    }

    /// Patterns for exactly `n` fields: surplus patterns nest into the last field
    /// (`(a, b, c)` on `A ∧ B ∧ C`), missing ones are wildcards.
    fn fit_fields(ps: &[RPat], n: usize) -> Vec<RPat> {
        if n == 0 {
            return vec![];
        }
        if ps.len() > n {
            let mut v: Vec<RPat> = ps[..n - 1].to_vec();
            v.push(RPat::Tuple(ps[n - 1..].to_vec()));
            v
        } else {
            let mut v = ps.to_vec();
            v.resize(n, RPat::Wild);
            v
        }
    }

    // ---- by_cases / by_contra ----

    pub(super) fn t_by_cases(
        &mut self,
        st: &mut Tac,
        g: Goal,
        name: Option<&Ident>,
        prop: &Expr,
        span: Span,
    ) -> R<Vec<Goal>> {
        if self.env.get("em").is_none() {
            return err(span, "`by_cases` needs classical logic (`em`)");
        }
        let p = self.elab_type(prop)?;
        self.solve_goals(false)?;
        let p = self.tc.zonk(&p);
        let p = self.devirt(&p);
        let pf = app(cnst("em".into(), vec![]), p);
        let ty = from_kernel(self.tc.infer(&pf), span)?;
        let ty = self.tc.zonk(&ty);
        let ng = self.add_hyp(st, &g, "_bycases", ty, pf);
        let hn = name.map_or("h".to_string(), |n| n.name.clone());
        let mut names = HashMap::new();
        names.insert("inl".to_string(), vec![hn.clone()]);
        names.insert("inr".to_string(), vec![hn]);
        let saved = self.case_names.replace(names);
        let r = self.t_induct(st, ng, &ident("_bycases", span), &[], None, false, span);
        self.case_names = saved;
        r
    }

    pub(super) fn t_by_contra(
        &mut self,
        st: &mut Tac,
        g: Goal,
        name: Option<&Ident>,
        span: Span,
    ) -> R<Vec<Goal>> {
        if self.env.get("by_contradiction").is_none() {
            return err(span, "`by_contra` needs classical logic");
        }
        let tgt = self.tc.zonk(&g.target);
        let hn = name.map_or("h".to_string(), |n| n.name.clone());
        let not_t = app(cnst("Not".into(), vec![]), tgt.clone());
        let fv = self.tc.fresh(&hn, not_t.clone(), Mult::Omega);
        let mut ng = self.new_goal(&g, cnst("False".into(), vec![]), "");
        ng.scope.push((hn, fvar(fv)));
        let lam_mv = self
            .tc
            .new_mvar(pi(Mult::Omega, not_t, cnst("False".into(), vec![])));
        st.sol.insert(mvar_id(&lam_mv), Sol::Lam(vec![fv], ng.mv));
        let pf = mk_apps(&cnst("by_contradiction".into(), vec![]), &[tgt, lam_mv]);
        self.solve(st, &g, pf);
        Ok(vec![ng])
    }

    // ---- specialize / refine ----

    pub(super) fn t_specialize(
        &mut self,
        st: &mut Tac,
        g: Goal,
        e: &Expr,
        span: Span,
    ) -> R<Vec<Goal>> {
        let head = match &e.kind {
            ExprKind::Var(n) => n.clone(),
            ExprKind::Call(f, _) => match &f.kind {
                ExprKind::Var(n) => n.clone(),
                _ => return err(span, "`specialize` needs `h(args)` with `h` a hypothesis"),
            },
            _ => return err(span, "`specialize` needs `h(args)` with `h` a hypothesis"),
        };
        if self.hyp_id(&g, &head).is_none() {
            return err(span, format!("`{head}` is not a hypothesis"));
        }
        let pf = self.elab_in_goal(e, None)?;
        if first_mvar(&pf).is_some() {
            return err(e.span, "cannot infer an argument of this term");
        }
        let ty = from_kernel(self.tc.infer(&pf), span)?;
        let ty = self.tc.zonk(&ty);
        let ty = self.devirt(&ty);
        Ok(vec![self.add_hyp(st, &g, &head, ty, pf)])
    }

    pub(super) fn t_refine(&mut self, st: &mut Tac, g: Goal, e: &Expr, span: Span) -> R<Vec<Goal>> {
        let tgt = g.target.clone();
        let pf = self.elab_in_goal(e, Some(&tgt))?;
        let mut ids = Vec::new();
        collect_mvars(&pf, &mut ids);
        let mut goals = Vec::new();
        for id in ids {
            let ty = from_kernel(self.tc.infer(&mvar(id)), span)?;
            let ty = self.tc.zonk(&ty);
            goals.push(Goal {
                mv: id,
                scope: g.scope.clone(),
                target: ty,
                tag: String::new(),
            });
        }
        self.solve(st, &g, pf);
        Ok(goals)
    }

    // ---- funext / congr ----

    pub(super) fn t_funext(
        &mut self,
        st: &mut Tac,
        g: Goal,
        names: &[Ident],
        span: Span,
    ) -> R<Vec<Goal>> {
        let Some((l, alpha, f, h)) = self.eq_parts(&g.target) else {
            return err(span, "`funext` needs a goal `f = g` between functions");
        };
        let alpha_w = from_kernel(self.tc.whnf(&alpha), span)?;
        let Term::Pi(m, dom, body) = &*alpha_w else {
            return err(span, "`funext` needs a goal `f = g` between functions");
        };
        let u = self.sort_level_of(dom, span)?;
        let x = self.tc.fresh("x", dom.clone(), *m);
        let bx = instantiate(body, &fvar(x));
        let v = self.sort_level_of(&bx, span)?;
        let beta = lam(*m, dom.clone(), body.clone());
        let applied = |fun: &T| app(fun.clone(), fvar(x));
        let eq_x = mk_apps(
            &cnst("Eq".into(), vec![v.clone()]),
            &[bx, applied(&f), applied(&h)],
        );
        let tgt = self.tc.mk_pi(&[x], &eq_x);
        let ng = self.new_goal(&g, tgt, "");
        let pf = mk_apps(
            &cnst("funext".into(), vec![u, v]),
            &[dom.clone(), beta, f, h, mvar(ng.mv)],
        );
        let _ = l;
        self.solve(st, &g, pf);
        let names: Vec<Ident> = if names.is_empty() {
            vec![ident("x", span)]
        } else {
            names.to_vec()
        };
        self.t_intro(st, ng, &names, span)
    }

    pub(super) fn t_congr(&mut self, st: &mut Tac, g: Goal, span: Span) -> R<Vec<Goal>> {
        let Some((l, alpha, a, b)) = self.eq_parts(&g.target) else {
            return err(span, "`congr` needs a goal `f a = f b`");
        };
        let (fa, aargs) = app_spine(&a);
        let (fb, bargs) = app_spine(&b);
        if aargs.len() != bargs.len() || aargs.is_empty() || !self.def_eq(&fa, &fb) {
            return err(
                span,
                "`congr` needs both sides to apply the same function to the same number of arguments",
            );
        }
        // replace the arguments one at a time, left to right
        let mut cur_args = aargs.clone();
        let mut goals = Vec::new();
        let mut proof = mk_apps(
            &cnst("Eq.refl".into(), vec![l.clone()]),
            &[alpha.clone(), a.clone()],
        );
        let mut cur = a.clone();
        for i in 0..aargs.len() {
            if self.def_eq(&aargs[i], &bargs[i]) {
                continue;
            }
            let ai_ty = from_kernel(self.tc.infer(&aargs[i]), span)?;
            let ai_ty = self.tc.zonk(&ai_ty);
            let lu = self.sort_level_of(&ai_ty, span)?;
            // goal ai = bi
            let eq_i = mk_apps(
                &cnst("Eq".into(), vec![lu.clone()]),
                &[ai_ty.clone(), aargs[i].clone(), bargs[i].clone()],
            );
            let ng = self.new_goal(&g, eq_i, "");
            // the function `fun x => head args[i := x]`
            let x = self.tc.fresh("x", ai_ty.clone(), Mult::Omega);
            let mut args_x = cur_args.clone();
            args_x[i] = fvar(x);
            let body = mk_apps(&fa, &args_x);
            let fun = self.tc.mk_lam(&[x], &body);
            let mut next_args = cur_args.clone();
            next_args[i] = bargs[i].clone();
            let next = mk_apps(&fa, &next_args);
            let step = mk_apps(
                &cnst("congr_arg".into(), vec![lu, l.clone()]),
                &[
                    ai_ty,
                    alpha.clone(),
                    aargs[i].clone(),
                    bargs[i].clone(),
                    fun,
                    mvar(ng.mv),
                ],
            );
            proof = mk_apps(
                &cnst("Eq.trans".into(), vec![l.clone()]),
                &[
                    alpha.clone(),
                    a.clone(),
                    cur.clone(),
                    next.clone(),
                    proof,
                    step,
                ],
            );
            goals.push(ng);
            cur_args = next_args;
            cur = next;
        }
        if goals.is_empty() {
            return err(span, "`congr`: the two sides are already equal; use `rfl`");
        }
        if let Err(e) = self.tc.infer(&proof) {
            return err(
                span,
                format!("`congr` could not build a congruence: {}", e.0),
            );
        }
        self.solve(st, &g, proof);
        Ok(goals)
    }

    // ---- calc ----

    fn calc_rel(&mut self, e: &Expr, prev: Option<&T>) -> R<(Rel, T, T)> {
        let side = |cx: &mut Self, x: &Expr, prev: Option<&T>| -> R<T> {
            if matches!(x.kind, ExprKind::Wild) {
                match prev {
                    Some(p) => Ok(p.clone()),
                    None => err(x.span, "the first step of a `calc` needs a left side"),
                }
            } else {
                cx.elab_in_goal(x, None)
            }
        };
        match &e.kind {
            ExprKind::Binary(BinOp::Eq, l, r) => {
                let l = side(self, l, prev)?;
                let r = side(self, r, None)?;
                Ok((Rel::Eq, l, r))
            }
            ExprKind::Call(f, args)
                if args.len() == 2
                    && matches!(&f.kind, ExprKind::Var(n) if n == "le" || n == "lt" || n == "LE.le") =>
            {
                let rel = match &f.kind {
                    ExprKind::Var(n) if n == "le" || n == "LE.le" => Rel::Le,
                    _ => Rel::Lt,
                };
                let l = side(self, &args[0], prev)?;
                let r = side(self, &args[1], None)?;
                Ok((rel, l, r))
            }
            _ => err(
                e.span,
                "a `calc` step must be `a = b`, `a <= b` or `lt(a, b)`",
            ),
        }
    }

    fn rel_prop(&mut self, rel: Rel, level: &Level, alpha: &T, a: &T, b: &T) -> T {
        match rel {
            Rel::Eq => mk_apps(
                &cnst("Eq".into(), vec![level.clone()]),
                &[alpha.clone(), a.clone(), b.clone()],
            ),
            Rel::Le => mk_apps(&cnst("le".into(), vec![]), &[a.clone(), b.clone()]),
            Rel::Lt => mk_apps(&cnst("lt".into(), vec![]), &[a.clone(), b.clone()]),
        }
    }

    fn calc_trans(&mut self, c1: Chain, c2: Chain, span: Span) -> R<Chain> {
        let (a, b, c) = (c1.lhs.clone(), c1.rhs.clone(), c2.rhs.clone());
        let l = c1.level.clone();
        let al = c1.alpha.clone();
        let mk = |n: &str, args: &[T]| mk_apps(&cnst(n.into(), vec![]), args);
        let (rel, proof) = match (c1.rel, c2.rel) {
            (Rel::Eq, Rel::Eq) => (
                Rel::Eq,
                mk_apps(
                    &cnst("Eq.trans".into(), vec![l.clone()]),
                    &[
                        al.clone(),
                        a.clone(),
                        b.clone(),
                        c.clone(),
                        c1.proof,
                        c2.proof,
                    ],
                ),
            ),
            (Rel::Eq, r) => {
                // a = b and R b c: transport R along b = a
                let x = self.tc.fresh("x", al.clone(), Mult::Omega);
                let body = self.rel_prop(r, &l, &al, &fvar(x), &c);
                let motive = self.tc.mk_lam(&[x], &body);
                let sym = mk_apps(
                    &cnst("Eq.symm".into(), vec![l.clone()]),
                    &[al.clone(), a.clone(), b.clone(), c1.proof],
                );
                (
                    r,
                    mk_apps(
                        &cnst("Eq.subst".into(), vec![l.clone()]),
                        &[al.clone(), b.clone(), a.clone(), motive, sym, c2.proof],
                    ),
                )
            }
            (r, Rel::Eq) => {
                let x = self.tc.fresh("x", al.clone(), Mult::Omega);
                let body = self.rel_prop(r, &l, &al, &a, &fvar(x));
                let motive = self.tc.mk_lam(&[x], &body);
                (
                    r,
                    mk_apps(
                        &cnst("Eq.subst".into(), vec![l.clone()]),
                        &[al.clone(), b.clone(), c.clone(), motive, c2.proof, c1.proof],
                    ),
                )
            }
            (Rel::Le, Rel::Le) => (
                Rel::Le,
                mk(
                    "le_trans",
                    &[a.clone(), b.clone(), c.clone(), c1.proof, c2.proof],
                ),
            ),
            (Rel::Lt, Rel::Lt) => (
                Rel::Lt,
                mk(
                    "lt_trans",
                    &[a.clone(), b.clone(), c.clone(), c1.proof, c2.proof],
                ),
            ),
            (Rel::Lt, Rel::Le) => (
                Rel::Lt,
                mk(
                    "lt_of_lt_of_le",
                    &[a.clone(), b.clone(), c.clone(), c1.proof, c2.proof],
                ),
            ),
            (Rel::Le, Rel::Lt) => (
                Rel::Lt,
                mk(
                    "lt_of_le_of_lt",
                    &[a.clone(), b.clone(), c.clone(), c1.proof, c2.proof],
                ),
            ),
        };
        if let Err(e) = self.tc.infer(&proof) {
            return err(span, format!("`calc`: cannot chain these steps: {}", e.0));
        }
        Ok(Chain {
            rel,
            level: l,
            alpha: al,
            lhs: a,
            rhs: c,
            proof,
        })
    }

    pub(super) fn t_calc(
        &mut self,
        st: &mut Tac,
        g: Goal,
        steps: &[CalcStep],
        span: Span,
    ) -> R<Vec<Goal>> {
        let mut acc: Option<Chain> = None;
        for step in steps {
            let prev = acc.as_ref().map(|c| c.rhs.clone());
            let (rel, l, r) = self.calc_rel(&step.rel, prev.as_ref())?;
            let alpha = from_kernel(self.tc.infer(&l), step.rel.span)?;
            let alpha = self.tc.zonk(&alpha);
            let level = self.sort_level_of(&alpha, step.rel.span)?;
            let prop = self.rel_prop(rel, &level, &alpha, &l, &r);
            let proof = match &step.proof {
                HaveProof::Term(e) => self.elab_in_goal(e, Some(&prop))?,
                HaveProof::Tactic(ts) => {
                    let saved = self.scope.clone();
                    let r = self.prove(&prop, ts, span);
                    self.scope = saved;
                    r?
                }
            };
            let chain = Chain {
                rel,
                level,
                alpha,
                lhs: l,
                rhs: r,
                proof,
            };
            acc = Some(match acc {
                None => chain,
                Some(prev) => self.calc_trans(prev, chain, span)?,
            });
        }
        let c = acc.expect("a calc has a step");
        let got = self.rel_prop(c.rel, &c.level, &c.alpha, &c.lhs, &c.rhs);
        if !self.def_eq(&got, &g.target) {
            return err(
                span,
                format!(
                    "`calc` proves `{}`, but the goal is `{}`",
                    self.pp_prop(&got),
                    self.pp_prop(&g.target)
                ),
            );
        }
        self.solve(st, &g, c.proof);
        Ok(vec![])
    }

    pub(super) fn t_trivial(&mut self, st: &mut Tac, g: Goal, span: Span) -> R<Vec<Goal>> {
        let mk = |kind| Tactic { kind, span };
        let true_intro = Expr {
            kind: ExprKind::Var("True.intro".into()),
            span,
        };
        let alts = vec![
            mk(TacticKind::Rfl),
            mk(TacticKind::Assumption),
            mk(TacticKind::Exact(true_intro)),
            mk(TacticKind::Decide),
            mk(TacticKind::Omega),
            mk(TacticKind::Simp(vec![], None)),
        ];
        self.run_on(st, g, &mk(TacticKind::First(alts)))
    }
}
