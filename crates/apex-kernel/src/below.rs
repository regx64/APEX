//! `T.below` and `T.brecOn`: course-of-values recursion, generated for every
//! simple inductive type (not a proposition, not indexed, not mutual).
//!
//! `T.below motive t` is the tuple of `motive s` for every strict subterm `s` of `t`
//! (nested `PProd`s), and `T.brecOn t F` computes `F t (below ...)` for all subterms at
//! once. A structurally recursive function with arbitrarily deep patterns is then
//! `brecOn` plus projections out of the `below` tuple. Both are ordinary definitions,
//! checked by the kernel like any other; nothing here is trusted.

use crate::env::*;
use crate::level::Level;
use crate::tc::TypeChecker;
use crate::term::*;

/// `PUnit` and `PProd` with their projections: the universe-polymorphic unit and pair.
pub(crate) fn add_pprod(env: &mut Env) -> KResult<()> {
    use crate::builder::*;
    use crate::inductive::InductiveDecl;
    let u = Level::param("u");
    let v = Level::param("v");
    env.add_inductive(InductiveDecl {
        name: "PUnit".into(),
        lparams: vec!["u".into()],
        nparams: 0,
        ty: sort_(u.clone()).build()?,
        ctors: vec![("PUnit.unit".into(), cl("PUnit", vec![u.clone()]).build()?)],
    })?;
    let max1 =
        |a: &Level, b: &Level| Level::max(Level::of_nat(1), Level::max(a.clone(), b.clone()));
    let pprod = |a: Raw, b: Raw| app_(cl("PProd", vec![u.clone(), v.clone()]), vec![a, b]);
    env.add_inductive(InductiveDecl {
        name: "PProd".into(),
        lparams: vec!["u".into(), "v".into()],
        nparams: 2,
        ty: pi_m(
            Mult::Zero,
            "α",
            sort_(u.clone()),
            pi_m(Mult::Zero, "β", sort_(v.clone()), sort_(max1(&u, &v))),
        )
        .build()?,
        ctors: vec![(
            "PProd.mk".into(),
            pi_m(
                Mult::Zero,
                "α",
                sort_(u.clone()),
                pi_m(
                    Mult::Zero,
                    "β",
                    sort_(v.clone()),
                    arrow(v_("α"), arrow(v_("β"), pprod(v_("α"), v_("β")))),
                ),
            )
            .build()?,
        )],
    })?;
    // PProd.fst / PProd.snd
    for (name, first) in [("PProd.fst", true), ("PProd.snd", false)] {
        let (res, lvl) = if first {
            ("α", u.clone())
        } else {
            ("β", v.clone())
        };
        env.add_def(
            name,
            &["u", "v"],
            pi_m(
                Mult::Zero,
                "α",
                sort_(u.clone()),
                pi_m(
                    Mult::Zero,
                    "β",
                    sort_(v.clone()),
                    arrow(pprod(v_("α"), v_("β")), v_(res)),
                ),
            )
            .build()?,
            lam_m(
                Mult::Zero,
                "α",
                sort_(u.clone()),
                lam_m(
                    Mult::Zero,
                    "β",
                    sort_(v.clone()),
                    lam_(
                        "p",
                        pprod(v_("α"), v_("β")),
                        app_(
                            cl("PProd.rec", vec![lvl, u.clone(), v.clone()]),
                            vec![
                                v_("α"),
                                v_("β"),
                                lam_("_", pprod(v_("α"), v_("β")), v_(res)),
                                lam_(
                                    "a",
                                    v_("α"),
                                    lam_("b", v_("β"), v_(if first { "a" } else { "b" })),
                                ),
                                v_("p"),
                            ],
                        ),
                    ),
                ),
            )
            .build()?,
        )?;
    }
    Ok(())
}

fn v_(n: &str) -> crate::builder::Raw {
    crate::builder::v(n)
}

impl Env {
    /// Generate `I.below` and `I.brecOn` for a simple inductive type; silently does
    /// nothing for the types it does not cover.
    pub(crate) fn add_below_brec(&mut self, ind: &str) -> KResult<()> {
        if self.get("PProd.snd").is_none() {
            return Ok(());
        }
        let info = match self.get(ind) {
            Some(Decl::Inductive(i)) => i.clone(),
            _ => return Ok(()),
        };
        if info.is_prop || info.nindices != 0 {
            return Ok(());
        }
        let rec_info = match self.get(&info.rec) {
            Some(Decl::Rec(r)) => r.clone(),
            _ => return Ok(()),
        };
        if rec_info.nmotives != 1 || rec_info.lparams.len() != info.lparams.len() + 1 {
            return Ok(());
        }
        let built = {
            let mut tc = TypeChecker::new(self);
            match build(&mut tc, self, ind, &info, &rec_info)? {
                Some(b) => b,
                None => return Ok(()),
            }
        };
        let lps: Vec<&str> = built.lparams.iter().map(|n| n.as_ref()).collect();
        self.add_def(
            &format!("{ind}.below"),
            &lps,
            built.below_ty,
            built.below_val,
        )?;
        self.add_def(
            &format!("{ind}.brecOn"),
            &lps,
            built.brec_ty,
            built.brec_val,
        )?;
        Ok(())
    }
}

struct Built {
    lparams: Vec<Name>,
    below_ty: T,
    below_val: T,
    brec_ty: T,
    brec_val: T,
}

fn build(
    tc: &mut TypeChecker,
    env: &Env,
    ind: &str,
    info: &IndInfo,
    _rec_info: &RecInfo,
) -> KResult<Option<Built>> {
    let mut u_name = String::from("u");
    while info.lparams.iter().any(|p| **p == *u_name) {
        u_name.push('\'');
    }
    let u = Level::Param(u_name.as_str().into());
    let ll = Level::max(Level::of_nat(1), u.clone()); // the sort of `below`
    let mut lparams: Vec<Name> = vec![u_name.as_str().into()];
    lparams.extend(info.lparams.iter().cloned());
    let ind_levels: Vec<Level> = info
        .lparams
        .iter()
        .map(|p| Level::Param(p.clone()))
        .collect();
    let pprod = |a: T, la: &Level, b: T, lb: &Level| {
        app(
            app(cnst("PProd".into(), vec![la.clone(), lb.clone()]), a),
            b,
        )
    };
    let pprod_mk = |a: T, la: &Level, b: T, lb: &Level, x: T, y: T| {
        mk_apps(
            &cnst("PProd.mk".into(), vec![la.clone(), lb.clone()]),
            &[a, b, x, y],
        )
    };
    let punit = cnst("PUnit".into(), vec![ll.clone()]);
    let punit_unit = cnst("PUnit.unit".into(), vec![ll.clone()]);

    let (pfv, _) = tc.telescope(&info.ty, Some(info.nparams))?;
    let pargs: Vec<T> = pfv.iter().map(|&i| fvar(i)).collect();
    let t_ty = mk_apps(&cnst(ind.into(), ind_levels.clone()), &pargs);
    let motive_ty = pi(Mult::Omega, t_ty.clone(), sort(u.clone()));
    let motive = tc.fresh("motive", motive_ty, Mult::Zero);
    let motive_t = fvar(motive);
    let t = tc.fresh("t", t_ty.clone(), Mult::Omega);

    // per constructor: fields, recursive fields
    struct Ctor {
        name: Name,
        fields: Vec<u32>,
        rec: Vec<usize>, // indices of direct recursive fields
    }
    let mut ctors = Vec::new();
    for cn in &info.ctors {
        let cty = env.const_type(cn, &ind_levels)?;
        let rest = tc.instantiate_pis(&cty, &pargs)?;
        let (fields, _) = tc.telescope(&rest, None)?;
        // linear/erased fields would make the generated terms violate multiplicities
        if fields
            .iter()
            .any(|&f| tc.local_mult(f) != Some(Mult::Omega))
        {
            return Ok(None);
        }
        let mut rec = Vec::new();
        for (j, &f) in fields.iter().enumerate() {
            let fty = tc.local_ty(f)?;
            if contains_const(&fty, ind) {
                if fty != t_ty {
                    return Ok(None); // higher-order or nested recursion: not covered
                }
                rec.push(j);
            }
        }
        ctors.push(Ctor {
            name: cn.clone(),
            fields,
            rec,
        });
    }

    let rec_const = |lvl: Level| {
        let mut ls = vec![lvl];
        ls.extend(ind_levels.iter().cloned());
        cnst(rec_info_name(info), ls)
    };

    // ---- below ----
    let below_motive = lam(Mult::Omega, t_ty.clone(), sort(ll.clone()));
    let mut below_minors = Vec::new();
    for c in &ctors {
        let ihs: Vec<u32> = c
            .rec
            .iter()
            .map(|_| tc.fresh("ih", sort(ll.clone()), Mult::Omega))
            .collect();
        let mut body = punit.clone();
        for (k, &j) in c.rec.iter().enumerate().rev() {
            let elem = pprod(
                app(motive_t.clone(), fvar(c.fields[j])),
                &u,
                fvar(ihs[k]),
                &ll,
            );
            body = pprod(elem, &ll, body, &ll);
        }
        below_minors.push(tc.mk_lam(&[c.fields.clone(), ihs].concat(), &body));
    }
    let below_app = |t: T| {
        mk_apps(
            &rec_const(Level::succ(ll.clone())),
            &[
                pargs.clone(),
                vec![below_motive.clone()],
                below_minors.clone(),
                vec![t],
            ]
            .concat(),
        )
    };
    let below_ty = tc.mk_pi(&[pfv.clone(), vec![motive, t]].concat(), &sort(ll.clone()));
    let below_val = tc.mk_lam(
        &[pfv.clone(), vec![motive, t]].concat(),
        &below_app(fvar(t)),
    );
    let below_const = cnst(
        format!("{ind}.below").into(),
        lparams.iter().map(|p| Level::Param(p.clone())).collect(),
    );
    let below_of = |tt: T| {
        mk_apps(
            &below_const,
            &[pargs.clone(), vec![motive_t.clone(), tt]].concat(),
        )
    };

    // ---- brecOn ----
    let pair_ty = |tt: T| pprod(app(motive_t.clone(), tt.clone()), &u, below_of(tt), &ll);
    let brec_motive = lam(Mult::Omega, t_ty.clone(), pair_ty(bvar(0)));
    let f_ty = {
        let tv = tc.fresh("t", t_ty.clone(), Mult::Omega);
        let bt = tc.fresh("b", below_of(fvar(tv)), Mult::Omega);
        let _ = bt;
        tc.mk_pi(&[tv, bt], &app(motive_t.clone(), fvar(tv)))
    };
    let f = tc.fresh("F", f_ty, Mult::Omega);
    let mut brec_minors = Vec::new();
    for c in &ctors {
        let ihs: Vec<u32> = c
            .rec
            .iter()
            .map(|&j| tc.fresh("ih", pair_ty(fvar(c.fields[j])), Mult::Omega))
            .collect();
        // below (c fs) as a tuple of the ihs
        let mut rest_ty = punit.clone();
        let mut bval = punit_unit.clone();
        for (k, &j) in c.rec.iter().enumerate().rev() {
            let elem_ty = pair_ty(fvar(c.fields[j]));
            bval = pprod_mk(
                elem_ty.clone(),
                &ll,
                rest_ty.clone(),
                &ll,
                fvar(ihs[k]),
                bval,
            );
            rest_ty = pprod(elem_ty, &ll, rest_ty, &ll);
        }
        let capp = mk_apps(
            &cnst(c.name.clone(), ind_levels.clone()),
            &[pargs.clone(), c.fields.iter().map(|&f| fvar(f)).collect()].concat(),
        );
        let fval = mk_apps(&fvar(f), &[capp.clone(), bval.clone()]);
        let body = pprod_mk(
            app(motive_t.clone(), capp.clone()),
            &u,
            below_of(capp),
            &ll,
            fval,
            bval,
        );
        brec_minors.push(tc.mk_lam(&[c.fields.clone(), ihs].concat(), &body));
    }
    let rec_app = mk_apps(
        &rec_const(ll.clone()),
        &[pargs.clone(), vec![brec_motive], brec_minors, vec![fvar(t)]].concat(),
    );
    let fst = mk_apps(
        &cnst("PProd.fst".into(), vec![u.clone(), ll.clone()]),
        &[app(motive_t.clone(), fvar(t)), below_of(fvar(t)), rec_app],
    );
    let binders = [pfv.clone(), vec![motive, t, f]].concat();
    let brec_ty = tc.mk_pi(&binders, &app(motive_t.clone(), fvar(t)));
    let brec_val = tc.mk_lam(&binders, &fst);
    Ok(Some(Built {
        lparams,
        below_ty,
        below_val,
        brec_ty,
        brec_val,
    }))
}

fn rec_info_name(info: &IndInfo) -> Name {
    info.rec.clone()
}
