//! Constructor equations: `contradiction` on `C1 .. = C2 ..` and `injection`.
//!
//! Both are built from a *Prop-valued case function* over the inductive type, the
//! `noConfusion` idea without a generated `noConfusionType`:
//!
//! * discrimination: `d x := match x { C1 .. => True, _ => False }`; transporting
//!   `True` along `h : C1 .. = C2 ..` proves `False`.
//! * injection: `p_j x := match x { C a1..an => a_j = field_j, _ => True }`;
//!   transporting `rfl : a_j = a_j` along `h : C as = C bs` proves `a_j = b_j`.
//!   Only fields whose type does not depend on earlier fields are injected.

use super::*;

/// Builds the result for a constructor from its fields.
type CaseFn<'f, 'a> = dyn FnMut(&mut Cx<'a>, &str, &[u32]) -> R<T> + 'f;

impl<'a> Cx<'a> {
    /// A constructor application: constructor name and all its arguments (parameters first).
    pub(super) fn ctor_view(&mut self, t: &T) -> Option<(String, Vec<T>)> {
        let t = self.tc.zonk(t);
        let w = self.tc.whnf(&t).ok()?;
        if let Term::Lit(n) = &*w {
            return Some(if *n == 0 {
                ("Nat.zero".to_string(), vec![])
            } else {
                (
                    "Nat.succ".to_string(),
                    vec![std::rc::Rc::new(Term::Lit(n - 1))],
                )
            });
        }
        let (h, args) = app_spine(&w);
        match &*h {
            Term::Const(n, _) => match self.env.get(n) {
                Some(Decl::Ctor(_)) => Some((n.to_string(), args)),
                _ => None,
            },
            _ => None,
        }
    }

    /// `fun (x : I params) => I.rec .. x`, with `case ctor fields` giving the (Prop-valued)
    /// result for each constructor. `None` if the type is indexed or a proposition.
    fn case_fn(
        &mut self,
        ctor: &str,
        ctor_args: &[T],
        ilevels: &[Level],
        case: &mut CaseFn<'_, 'a>,
        span: Span,
    ) -> R<Option<T>> {
        let Some(Decl::Ctor(ci)) = self.env.get(ctor) else {
            return Ok(None);
        };
        let (iname, nparams) = (ci.ind.to_string(), ci.nparams);
        let Some(Decl::Inductive(info)) = self.env.get(&iname) else {
            return Ok(None);
        };
        let info = info.clone();
        if info.nindices > 0 || info.is_prop {
            return Ok(None);
        }
        let Some(Decl::Rec(rinfo)) = self.env.get(&info.rec) else {
            return Ok(None);
        };
        if rinfo.lparams.len() != info.lparams.len() + 1 {
            return Ok(None);
        }
        let params: Vec<T> = ctor_args[..nparams].to_vec();
        // results are propositions (`Prop : Sort 1`), so the recursor eliminates into `Sort 1`
        let mut rec_levels = vec![Level::zero().succ()];
        rec_levels.extend(ilevels.iter().cloned());
        let xty = mk_apps(&cnst(iname.as_str().into(), ilevels.to_vec()), &params);
        let x = self.tc.fresh("x", xty.clone(), Mult::Omega);
        let mut motives = Vec::new();
        for fname in &info.family {
            let kt = mk_apps(&cnst(fname.clone(), ilevels.to_vec()), &params);
            motives.push(lam(Mult::Omega, kt, sort(Level::zero())));
        }
        let mut rty = from_kernel(self.env.const_type(&info.rec, &rec_levels), span)?;
        for p in params.iter().chain(motives.iter()) {
            match &*rty {
                Term::Pi(_, _, b) => rty = instantiate(b, p),
                _ => return err(span, "internal error: malformed recursor type"),
            }
        }
        let mut minors = Vec::new();
        for fname in &info.family {
            let fctors: Vec<Name> = match self.env.get(fname) {
                Some(Decl::Inductive(i)) => i.ctors.clone(),
                _ => return err(span, "internal error: missing family member"),
            };
            for cn in &fctors {
                let nfields = match self.env.get(cn) {
                    Some(Decl::Ctor(c)) => c.nfields,
                    _ => return err(span, "internal error: missing constructor"),
                };
                let (dom, rest) = match &*rty {
                    Term::Pi(_, d, b) => (d.clone(), b.clone()),
                    _ => return err(span, "internal error: malformed recursor type"),
                };
                // telescope by hand: the conclusion is `Prop`-typed, which must not be unfolded
                let mut bs = Vec::new();
                let mut cur = head_beta(&dom);
                while let Term::Pi(m, d, b) = &*cur.clone() {
                    let fv = self.tc.fresh("a", head_beta(d), *m);
                    bs.push(fv);
                    cur = instantiate(b, &fvar(fv));
                }
                let body = case(self, cn, &bs[..nfields])?;
                let m = self.tc.mk_lam(&bs, &body);
                rty = instantiate(&rest, &m);
                minors.push(m);
            }
        }
        let mut args = params;
        args.extend(motives);
        args.extend(minors);
        args.push(fvar(x));
        let body = mk_apps(&cnst(info.rec.clone(), rec_levels), &args);
        Ok(Some(self.tc.mk_lam(&[x], &body)))
    }

    /// If `h : C1 .. = C2 ..` with different constructors, a proof of `False`.
    pub(super) fn discriminate(&mut self, h: &T, hty: &T, span: Span) -> R<Option<T>> {
        let Some((l, alpha, a, b)) = self.eq_parts(hty) else {
            return Ok(None);
        };
        let (Some((c1, args1)), Some((c2, _))) = (self.ctor_view(&a), self.ctor_view(&b)) else {
            return Ok(None);
        };
        if c1 == c2 {
            return Ok(None);
        }
        let (_, ls) = {
            let w = self.tc.whnf(&self.tc.zonk(&alpha)).ok();
            match w.as_ref().map(app_spine) {
                Some((hd, _)) => match &*hd {
                    Term::Const(n, ls) => (n.clone(), ls.clone()),
                    _ => return Ok(None),
                },
                None => return Ok(None),
            }
        };
        let true_ = cnst("True".into(), vec![]);
        let false_ = cnst("False".into(), vec![]);
        let c1n = c1.clone();
        let Some(disc) = self.case_fn(
            &c1,
            &args1,
            &ls,
            &mut |_, c, _| {
                Ok(if c == c1n {
                    true_.clone()
                } else {
                    false_.clone()
                })
            },
            span,
        )?
        else {
            return Ok(None);
        };
        let pf = mk_apps(
            &cnst("Eq.subst".into(), vec![l]),
            &[
                alpha,
                a,
                b,
                disc,
                h.clone(),
                cnst("True.intro".into(), vec![]),
            ],
        );
        if self.tc.infer(&pf).is_err() {
            return Ok(None);
        }
        Ok(Some(pf))
    }

    /// `injection h with n1 n2`: the field equations of `h : C as = C bs`.
    pub(super) fn t_injection(
        &mut self,
        st: &mut Tac,
        g: Goal,
        h: &Expr,
        names: &[Ident],
        span: Span,
    ) -> R<Vec<Goal>> {
        let hp = self.elab_in_goal(h, None)?;
        let hty = from_kernel(self.tc.infer(&hp), span)?;
        let hty = self.tc.zonk(&hty);
        let Some((l, alpha, a, b)) = self.eq_parts(&hty) else {
            return err(
                span,
                "`injection` needs an equation between constructor applications",
            );
        };
        let (Some((c1, args1)), Some((c2, args2))) = (self.ctor_view(&a), self.ctor_view(&b))
        else {
            return err(
                span,
                "`injection`: both sides must be constructor applications",
            );
        };
        if c1 != c2 {
            // different constructors: the goal follows from a contradiction
            if let Some(pf) = self.discriminate(&hp, &hty, span)? {
                let tgt = self.tc.zonk(&g.target);
                let lvl = self.sort_level_of(&tgt, span)?;
                self.solve(
                    st,
                    &g,
                    mk_apps(&cnst("False.elim".into(), vec![lvl]), &[tgt, pf]),
                );
                return Ok(vec![]);
            }
            return err(span, "`injection`: the constructors differ");
        }
        let (nparams, nfields, iname) = match self.env.get(&c1) {
            Some(Decl::Ctor(c)) => (c.nparams, c.nfields, c.ind.to_string()),
            _ => return err(span, "internal error: missing constructor"),
        };
        let ls = match &*app_spine(
            &self
                .tc
                .whnf(&self.tc.zonk(&alpha))
                .map_err(|e| ElabError::new(span, e.0))?,
        )
        .0
        {
            Term::Const(_, ls) => ls.clone(),
            _ => return err(span, "`injection`: unsupported type"),
        };
        let _ = iname;
        let mut cur = g;
        let mut count = 0;
        for j in 0..nfields {
            let (aj, bj) = (args1[nparams + j].clone(), args2[nparams + j].clone());
            let jj = j;
            let aj2 = aj.clone();
            let c1n = c1.clone();
            let mut dependent = false;
            let eq_level;
            let tau = {
                let t = from_kernel(self.tc.infer(&aj), span)?;
                self.tc.zonk(&t)
            };
            {
                eq_level = self.sort_level_of(&tau, span)?;
            }
            let eq_l = eq_level.clone();
            let tau2 = tau.clone();
            let Some(pj) = self.case_fn(
                &c1,
                &args1,
                &ls,
                &mut |cx, c, fields| {
                    if c != c1n {
                        return Ok(cnst("True".into(), vec![]));
                    }
                    // the field must not depend on earlier fields
                    let fty = cx
                        .tc
                        .local_ty(fields[jj])
                        .map_err(|e| ElabError::new(span, e.0))?;
                    if fields[..jj].iter().any(|&f| contains_fvar(&fty, f)) {
                        dependent = true;
                    }
                    Ok(mk_apps(
                        &cnst("Eq".into(), vec![eq_l.clone()]),
                        &[tau2.clone(), aj2.clone(), fvar(fields[jj])],
                    ))
                },
                span,
            )?
            else {
                return err(span, "`injection` is not supported for this type");
            };
            if dependent {
                continue;
            }
            let refl = mk_apps(
                &cnst("Eq.refl".into(), vec![eq_level.clone()]),
                &[tau.clone(), aj.clone()],
            );
            let pf = mk_apps(
                &cnst("Eq.subst".into(), vec![l.clone()]),
                &[alpha.clone(), a.clone(), b.clone(), pj, hp.clone(), refl],
            );
            let ety = mk_apps(&cnst("Eq".into(), vec![eq_level]), &[tau, aj, bj]);
            if self.tc.infer(&pf).is_err() {
                continue;
            }
            let name = names
                .get(count)
                .map(|n| n.name.clone())
                .unwrap_or_else(|| format!("h{}", count + 1));
            count += 1;
            cur = self.add_hyp(st, &cur, &name, ety, pf);
        }
        if count == 0 {
            return err(span, "`injection` found no field equations");
        }
        Ok(vec![cur])
    }
}
