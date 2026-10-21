//! `conv`: rewrite inside one subterm.
//!
//! `conv { lhs; arg 2; rw [h] }` focuses on a subterm `s` of the goal, proves `s = ?s'` with the
//! tactics (the goal `s = ?s'` is closed by `rfl`, which fixes `?s'`), and replaces `s` by `s'`
//! in the goal with `Eq.subst`. `conv at h { .. }` does the same inside the hypothesis `h`.

use super::*;

impl<'a> Cx<'a> {
    fn conv_focus(&mut self, root: &T, nav: &[NavStep], span: Span) -> R<T> {
        let mut cur = self.tc.zonk(root);
        for (i, step) in nav.iter().enumerate() {
            cur = match step {
                NavStep::Lhs | NavStep::Rhs => {
                    let Some((_, _, a, b)) = self.eq_parts(&cur) else {
                        return err(span, "`lhs`/`rhs` need an equation");
                    };
                    if matches!(step, NavStep::Lhs) {
                        self.tc.zonk(&a)
                    } else {
                        self.tc.zonk(&b)
                    }
                }
                NavStep::Fun => {
                    let (h, args) = app_spine(&cur);
                    if args.is_empty() {
                        return err(span, "`fun` needs an application");
                    }
                    mk_apps(&h, &args[..args.len() - 1])
                }
                NavStep::Arg(k) => {
                    let (h, args) = app_spine(&cur);
                    let mask: Vec<Bk> = match &*h {
                        Term::Const(n, _) => self.masks.get(&**n).cloned().unwrap_or_default(),
                        _ => vec![],
                    };
                    let explicit: Vec<&T> = args
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| mask.get(*j).is_none_or(|b| matches!(b, Bk::Exp)))
                        .map(|(_, a)| a)
                        .collect();
                    match k.checked_sub(1).and_then(|k| explicit.get(k)) {
                        Some(a) => (*a).clone(),
                        None => {
                            return err(
                                span,
                                format!(
                                    "`arg {k}`: step {} has only {} arguments",
                                    i + 1,
                                    explicit.len()
                                ),
                            )
                        }
                    }
                }
            };
        }
        Ok(cur)
    }

    pub(super) fn t_conv(
        &mut self,
        st: &mut Tac,
        g: Goal,
        at: Option<&Ident>,
        nav: &[NavStep],
        body: &[Tactic],
        span: Span,
    ) -> R<Vec<Goal>> {
        // the term we work in: the goal, or the type of a hypothesis
        let hyp = match at {
            Some(h) => {
                let Some(pos) = g.scope.iter().rposition(|(n, _)| plain_name(n) == h.name) else {
                    return err(h.span, format!("unknown hypothesis `{}`", h.name));
                };
                let Term::FVar(id) = &*g.scope[pos].1 else {
                    return err(h.span, format!("`{}` is not a hypothesis", h.name));
                };
                let ty = from_kernel(self.tc.local_ty(*id), span)?;
                Some((pos, *id, self.tc.zonk(&ty)))
            }
            None => None,
        };
        let root = match &hyp {
            Some((_, _, ty)) => ty.clone(),
            None => self.tc.zonk(&g.target),
        };
        let s = self.conv_focus(&root, nav, span)?;
        let sty = from_kernel(self.tc.infer(&s), span)?;
        let sty = self.tc.zonk(&sty);
        let lvl = self.sort_level_of(&sty, span)?;
        let m = self.tc.new_mvar(sty.clone());
        let eq = mk_apps(
            &cnst("Eq".into(), vec![lvl.clone()]),
            &[sty.clone(), s.clone(), m.clone()],
        );
        let gc = self.new_goal(&g, eq, "");
        let proof = mvar(gc.mv);
        // run the tactics on `s = ?m`, then close what is left by `rfl`
        let rest = std::mem::replace(&mut st.goals, vec![gc]);
        let mut r = self.run_seq(st, body);
        if r.is_ok() && !st.goals.is_empty() {
            let g1 = st.goals.remove(0);
            self.scope = g1.scope.clone();
            r = self
                .step(
                    st,
                    g1,
                    &Tactic {
                        kind: TacticKind::Rfl,
                        span,
                    },
                )
                .map(|more| st.goals.extend(more));
        }
        let leftover = std::mem::replace(&mut st.goals, rest);
        r?;
        if let Some(l) = leftover.first() {
            return err(span, format!("`conv` left a goal:\n{}", self.show_goal(l)));
        }
        let s2 = self.tc.zonk(&m);
        if matches!(&*s2, Term::MVar(_)) {
            return err(span, "`conv` did not determine the new subterm");
        }
        let abs = replace_term(&root, &s, 0);
        let new_root = instantiate(&abs, &s2);
        let motive = lam(Mult::Omega, sty.clone(), abs);
        match hyp {
            None => {
                let ng = self.new_goal(&g, new_root, "");
                let sym = mk_apps(
                    &cnst("Eq.symm".into(), vec![lvl.clone()]),
                    &[sty.clone(), s.clone(), s2.clone(), proof],
                );
                let pf = mk_apps(
                    &cnst("Eq.subst".into(), vec![lvl]),
                    &[sty, s2, s, motive, sym, mvar(ng.mv)],
                );
                if let Err(e) = self.tc.infer(&pf) {
                    return err(span, format!("`conv` produced an ill-typed proof: {}", e.0));
                }
                self.solve(st, &g, pf);
                // like Lean, finish with `rfl` when the conversion already settled the goal
                if self.try_rfl(st, &ng) {
                    return Ok(vec![]);
                }
                Ok(vec![ng])
            }
            Some((pos, id, _)) => {
                let name = g.scope[pos].0.clone();
                let new_h = self.tc.fresh(plain_name(&name), new_root, Mult::Omega);
                let mut ng = self.new_goal(&g, g.target.clone(), "");
                ng.scope[pos] = (name, fvar(new_h));
                let pf_h = mk_apps(
                    &cnst("Eq.subst".into(), vec![lvl]),
                    &[sty, s, s2, motive, proof, fvar(id)],
                );
                if let Err(e) = self.tc.infer(&pf_h) {
                    return err(span, format!("`conv` produced an ill-typed proof: {}", e.0));
                }
                let new_ty = from_kernel(self.tc.local_ty(new_h), span)?;
                let lam_mv = self.tc.new_mvar(pi(Mult::Omega, new_ty, g.target.clone()));
                st.sol
                    .insert(mvar_id(&lam_mv), Sol::Lam(vec![new_h], ng.mv));
                self.solve(st, &g, app(lam_mv, pf_h));
                Ok(vec![ng])
            }
        }
    }
}
