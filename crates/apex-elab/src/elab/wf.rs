//! Well-founded recursion: `fn f(..) termination_by m(..) decreasing_by { .. } { .. }`.
//!
//! `f` is defined through `WellFounded.fix` on `Nat` with `lt`, over the measure value
//! `n`. The step function takes `n`, a function `ih` for recursive calls, the
//! parameters, and a proof `hm : m(params) = n`:
//!
//! ```text
//! f params := fix lt_wf (fun n ih params hm => body) (m params) params rfl
//! ```
//!
//! A recursive call `f(b)` in the body becomes `ih (m b) pf b rfl` where `pf : m b < n`
//! comes from the `decreasing_by` tactic block (default `omega`) run in the context of
//! the call, including `if` conditions as hypotheses. The kernel cannot compute through
//! `fix` (the accessibility proof is opaque), so a second elaboration of the body, with
//! recursive calls left as plain calls, gives the *unfolding equation* `f.eq`, proved
//! from `WellFounded.fix_eq`. The interpreter runs `fix` as an ordinary fixpoint.

use super::*;

/// The context of a function being defined by well-founded recursion.
#[derive(Clone)]
pub(super) struct WfCtx {
    /// The measure value of the current call.
    pub n: u32,
    /// Recursive calls: `ih : ∀ m, lt m n → C m`.
    pub ih: u32,
    pub measure: Expr,
    pub tactics: Vec<Tactic>,
    /// Parameter names and variables.
    pub params: Vec<(String, u32)>,
    /// While elaborating the body for the unfolding equation: recursive calls are
    /// plain applications of this variable.
    pub plain: Option<u32>,
}

/// A compiled function: its type, its value, and which binders are implicit.
pub(super) type FnParts = (T, T, Vec<Bk>);

/// What the unfolding equation needs besides the definition itself.
pub(super) struct WfEq {
    pub ty: T,
    pub val: T,
}

const SELF: &str = "__wf_self";

fn nat() -> T {
    cnst("Nat".into(), vec![])
}

fn replace_fvar(t: &T, id: u32, with: &T) -> T {
    instantiate(&abstract_fvars(t, &[id]), with)
}

pub(super) fn rename_const(t: &T, from: &str, to: &str) -> T {
    match &**t {
        Term::Const(n, ls) if &**n == from => cnst(to.into(), ls.clone()),
        Term::App(f, a) => app(rename_const(f, from, to), rename_const(a, from, to)),
        Term::Lam(m, ty, b) => lam(*m, rename_const(ty, from, to), rename_const(b, from, to)),
        Term::Pi(m, ty, b) => pi(*m, rename_const(ty, from, to), rename_const(b, from, to)),
        Term::Let(m, ty, v, b) => let_(
            *m,
            rename_const(ty, from, to),
            rename_const(v, from, to),
            rename_const(b, from, to),
        ),
        _ => t.clone(),
    }
}

impl<'a> Cx<'a> {
    /// A recursive call inside a well-founded definition.
    pub(super) fn elab_wf_call(
        &mut self,
        wf: WfCtx,
        args: &[Expr],
        _exp: Option<&T>,
        span: Span,
    ) -> R<T> {
        if args.len() != wf.params.len() {
            return err(
                span,
                "a recursive call must supply all of the function's arguments",
            );
        }
        let ids: Vec<u32> = wf.params.iter().map(|(_, v)| *v).collect();
        let mut vals: Vec<T> = Vec::new();
        for (i, (_, v)) in wf.params.iter().enumerate() {
            let pty = from_kernel(self.tc.local_ty(*v), span)?;
            let pty = self.tc.zonk(&pty);
            let pty = vals
                .iter()
                .enumerate()
                .fold(pty, |t, (j, val)| replace_fvar(&t, ids[j], val));
            let a = self.elab_check(&args[i], &pty)?;
            vals.push(self.tc.zonk(&a));
        }
        self.solve_goals(false)?;
        let vals: Vec<T> = vals.iter().map(|v| self.tc.zonk(v)).collect();
        if let Some(fself) = wf.plain {
            return Ok(mk_apps(&fvar(fself), &vals));
        }
        // the measure at the call, with the parameters bound to the arguments
        let depth = self.scope.len();
        for ((name, _), val) in wf.params.iter().zip(&vals) {
            self.scope.push((name.clone(), val.clone()));
        }
        let mb = self.elab_check(&wf.measure, &nat());
        self.scope.truncate(depth);
        let mb = mb?;
        self.solve_goals(false)?;
        let mb = self.tc.zonk(&mb);
        let mb = self.devirt(&mb);
        // the obligation: the measure decreases
        let goal = mk_apps(&cnst("lt".into(), vec![]), &[mb.clone(), fvar(wf.n)]);
        let pf = self.prove(&goal, &wf.tactics, span).map_err(|mut e| {
            e.msg = format!(
                "cannot prove that this recursive call decreases the measure (`{}` < the current measure)\n{}",
                self.pp(&mb),
                e.msg
            );
            e.span = span;
            e
        })?;
        let refl = mk_apps(
            &cnst("Eq.refl".into(), vec![Level::of_nat(1)]),
            &[nat(), mb.clone()],
        );
        Ok(mk_apps(
            &fvar(wf.ih),
            &[vec![mb, pf], vals, vec![refl]].concat(),
        ))
    }
}

impl Elaborator {
    /// Define `f` by well-founded recursion on `measure`. Returns the definition and,
    /// when it can be built, the unfolding equation (terms mentioning `__wf_self`).
    pub(super) fn try_fn_wf(
        &self,
        f: &FnDecl,
        span: Span,
        measure: &Expr,
        decreasing: Option<&[apex_syntax::Token]>,
    ) -> R<(FnParts, Option<WfEq>)> {
        let tactics = match decreasing {
            Some(toks) => apex_syntax::parse_tactics(toks, span, &self.tables.notations)
                .map_err(|e| ElabError::new(e.span, e.msg))?,
            None => vec![Tactic {
                kind: TacticKind::Omega,
                span,
            }],
        };
        let mut cx = self.cx();
        cx.dep_if = true;
        let (mut fvs, mut mask) = cx.elab_binders(&f.generics, &[])?;
        let ngen = fvs.len();
        let (pf, pm) = cx.elab_binders(&[], &f.params)?;
        let explicit = pf.clone();
        fvs.extend(pf);
        mask.extend(pm);
        let ret = match &f.ret {
            Some(t) => cx.elab_type(t)?,
            None => cx.unit_type(),
        };
        let m_term = cx.elab_check(measure, &nat())?;
        cx.solve_goals(true)?;
        let m_term = {
            let z = cx.tc.zonk(&m_term);
            cx.devirt(&z)
        };
        let n = cx.tc.fresh("n", nat(), Mult::Omega);
        let eq_nat =
            |a: T, b: T| mk_apps(&cnst("Eq".into(), vec![Level::of_nat(1)]), &[nat(), a, b]);
        let hm = cx
            .tc
            .fresh("hm", eq_nat(m_term.clone(), fvar(n)), Mult::Omega);
        // C m := ∀ params, m(params) = m → ret
        let mfv = cx.tc.fresh("m", nat(), Mult::Omega);
        let hm_m = cx
            .tc
            .fresh("hm", eq_nat(m_term.clone(), fvar(mfv)), Mult::Omega);
        cx.tc.zonk_locals();
        let ret_z = cx.tc.zonk(&ret);
        let c_body = cx
            .tc
            .mk_pi(&[explicit.clone(), vec![hm_m]].concat(), &ret_z);
        let lvl = from_kernel(cx.tc.check_is_type(&c_body), span)?;
        let lvl = cx.tc.zonk_level(&lvl);
        let c_lam = lam(Mult::Omega, nat(), abstract_fvars(&c_body, &[mfv]));
        let lt = |a: T, b: T| mk_apps(&cnst("lt".into(), vec![]), &[a, b]);
        let m2 = cx.tc.fresh("m", nat(), Mult::Omega);
        let h2 = cx.tc.fresh("h", lt(fvar(m2), fvar(n)), Mult::Omega);
        let ih_ty = cx.tc.mk_pi(&[m2, h2], &app(c_lam.clone(), fvar(m2)));
        let ih = cx.tc.fresh("ih", ih_ty, Mult::Omega);

        let Some(block) = &f.body else {
            return err(f.name.span, "a function needs a body");
        };
        let names: Vec<(String, u32)> = f
            .params
            .iter()
            .zip(&explicit)
            .map(|(p, v)| (p.name.name.clone(), *v))
            .collect();
        let elab_body = |cx: &mut Cx, plain: Option<u32>| -> R<T> {
            cx.rec = Some(RecCtx {
                name: f.name.name.clone(),
                decr: u32::MAX,
                explicit: explicit.clone(),
                fields: HashMap::new(),
                refined: Vec::new(),
                in_top: false,
                deep: None,
                mutual: None,
                wf: Some(WfCtx {
                    n,
                    ih,
                    measure: measure.clone(),
                    tactics: tactics.clone(),
                    params: names.clone(),
                    plain,
                }),
            });
            let depth = cx.scope.len();
            cx.scope.push(("_n".into(), fvar(n)));
            cx.scope.push(("_hm".into(), fvar(hm)));
            let body = cx.scoped(|cx| {
                let v = cx.elab_block_opts(block, Some(&ret), true)?;
                cx.coerce(v, &ret, block.span)
            });
            cx.scope.truncate(depth);
            cx.solve_goals(true)?;
            body
        };
        let body = elab_body(&mut cx, None)?;
        cx.tc.zonk_locals();
        let body = cx.tc.zonk(&body);
        // F := fun n ih params hm => body
        let step = cx
            .tc
            .mk_lam(&[vec![n, ih], explicit.clone(), vec![hm]].concat(), &body);
        let lt_wf = cnst("lt_wf".into(), vec![]);
        let fix_const = cnst(
            "WellFounded.fix".into(),
            vec![Level::of_nat(1), lvl.clone()],
        );
        let fix_at = |x: T| {
            mk_apps(
                &fix_const,
                &[
                    nat(),
                    cnst("lt".into(), vec![]),
                    c_lam.clone(),
                    lt_wf.clone(),
                    step.clone(),
                    x,
                ],
            )
        };
        let refl = mk_apps(
            &cnst("Eq.refl".into(), vec![Level::of_nat(1)]),
            &[nat(), m_term.clone()],
        );
        let explicit_terms: Vec<T> = explicit.iter().map(|&e| fvar(e)).collect();
        let value = mk_apps(
            &fix_at(m_term.clone()),
            &[explicit_terms.clone(), vec![refl.clone()]].concat(),
        );

        // ---- the unfolding equation ----
        let eq = (|| -> R<WfEq> {
            let fself_ty = cx.tc.mk_pi(&explicit, &ret_z);
            let fself = cx.tc.fresh("f", fself_ty, Mult::Omega);
            let plain = elab_body(&mut cx, Some(fself))?;
            cx.tc.zonk_locals();
            let plain = cx.tc.zonk(&plain);
            let gens: Vec<T> = fvs[..ngen].iter().map(|&g| fvar(g)).collect();
            let self_app = mk_apps(&cnst(SELF.into(), vec![]), &gens);
            let lhs = mk_apps(&fvar(fself), &explicit_terms);
            let ret_lvl = from_kernel(cx.tc.check_is_type(&ret_z), span)?;
            let ret_lvl = cx.tc.zonk_level(&ret_lvl);
            let eq_prop = mk_apps(
                &cnst("Eq".into(), vec![ret_lvl.clone()]),
                &[ret_z.clone(), lhs, plain],
            );
            let eq_prop = replace_fvar(&eq_prop, fself, &self_app);
            let b_val = mk_apps(
                &step,
                &[
                    m_term.clone(),
                    lam(
                        Mult::Omega,
                        nat(),
                        lam(
                            Mult::Omega,
                            mk_apps(&cnst("lt".into(), vec![]), &[bvar(0), m_term.clone()]),
                            fix_at(bvar(1)),
                        ),
                    ),
                ],
            );
            let eq1 = mk_apps(
                &cnst(
                    "WellFounded.fix_eq".into(),
                    vec![Level::of_nat(1), lvl.clone()],
                ),
                &[
                    nat(),
                    cnst("lt".into(), vec![]),
                    c_lam.clone(),
                    lt_wf.clone(),
                    step.clone(),
                    m_term.clone(),
                ],
            );
            let c_m = app(c_lam.clone(), m_term.clone());
            let proj = lam(
                Mult::Omega,
                c_m.clone(),
                mk_apps(
                    &bvar(0),
                    &[explicit_terms.clone(), vec![refl.clone()]].concat(),
                ),
            );
            let eq2 = mk_apps(
                &cnst("congr_arg".into(), vec![lvl.clone(), ret_lvl]),
                &[c_m, ret_z.clone(), fix_at(m_term.clone()), b_val, proj, eq1],
            );
            Ok(WfEq {
                ty: cx.close(&fvs, &eq_prop, true, span)?,
                val: cx.close(&fvs, &eq2, false, span)?,
            })
        })()
        .ok();

        cx.borrow_check(f)?;
        let ret_full = ret_z;
        Ok((
            (
                cx.close(&fvs, &ret_full, true, span)?,
                cx.close(&fvs, &value, false, span)?,
                mask,
            ),
            eq,
        ))
    }

    /// Define `f` by well-founded recursion, with the user's measure or a guessed one.
    pub(super) fn elab_wf_fn(&mut self, f: &FnDecl, span: Span) -> R<()> {
        self.load_omega();
        let callee = callee_of(f, &[]).map_err(sig_error)?;
        let result = match &f.wf {
            Some(spec) => self.try_fn_wf(f, span, &spec.measure, spec.decreasing.as_deref())?,
            None => {
                // guess: each parameter in turn
                let mut first_err = None;
                let mut found = None;
                for p in &f.params {
                    let measure = Expr {
                        kind: ExprKind::Var(p.name.name.clone()),
                        span: p.name.span,
                    };
                    match self.try_fn_wf(f, span, &measure, None) {
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
                        let mut e = first_err.unwrap_or(ElabError::new(
                            f.name.span,
                            "a recursive function needs a parameter to recurse on",
                        ));
                        e.msg = format!(
                            "{}\nhelp: this is neither structurally recursive nor provably terminating with a \
                             parameter as the measure; add `termination_by <measure>` (and \
                             `decreasing_by {{ .. }}`)",
                            e.msg
                        );
                        return Err(e);
                    }
                }
            }
        };
        let ((ty, val, mask), eq) = result;
        let qname = self.qualified(&f.name);
        let kname = self.add_def_named(&qname, ty, val, mask.clone())?;
        self.tables.sigs.insert(kname.clone(), callee);
        if let Some(eq) = eq {
            let ty = rename_const(&eq.ty, SELF, &kname);
            let val = rename_const(&eq.val, SELF, &kname);
            let eq_name = Ident {
                name: format!("{}.eq", qname.name),
                span: f.name.span,
            };
            // best effort: the equation is a convenience, the definition stands without it
            let _ = self.add_def_named(&eq_name, ty, val, mask);
        }
        Ok(())
    }
}
