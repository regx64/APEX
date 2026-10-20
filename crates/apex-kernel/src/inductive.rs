//! Inductive types: validation (positivity, universes) and generation of
//! constructors' metadata, the recursor and its ι-rules.

use crate::env::*;
use crate::level::Level;
use crate::tc::TypeChecker;
use crate::term::*;

pub struct InductiveDecl {
    pub name: Name,
    pub lparams: Vec<Name>,
    pub nparams: usize,
    pub ty: T,
    pub ctors: Vec<(Name, T)>,
}

struct CtorAnalysis {
    fields: Vec<u32>,
    /// Per field: `Some((xs, js))` if recursive — `Π xs, I params js`.
    recs: Vec<Option<(Vec<u32>, Vec<T>)>>,
    res_indices: Vec<T>,
    field_is_prop: Vec<bool>,
}

impl<'a> TypeChecker<'a> {
    fn analyze_rec_field(
        &mut self,
        fty: &T,
        ind: &str,
        levels: &[Level],
        pargs: &[T],
    ) -> KResult<Option<(Vec<u32>, Vec<T>)>> {
        if !contains_const(fty, ind) {
            return Ok(None);
        }
        let (xs, res) = self.telescope(fty, None)?;
        for &x in &xs {
            if contains_const(&self.local_ty(x)?, ind) {
                return kerr(format!(
                    "non-positive occurrence of `{ind}` (strict positivity violation)"
                ));
            }
        }
        let (head, args) = app_spine(&res);
        let ok = matches!(&*head, Term::Const(n, ls) if &**n == ind && ls == levels)
            && args.len() >= pargs.len();
        if !ok {
            return kerr(format!(
                "invalid occurrence of `{ind}` in constructor field"
            ));
        }
        if args[..pargs.len()] != *pargs {
            return kerr(format!(
                "recursive occurrence of `{ind}` must use the same parameters"
            ));
        }
        let js = args[pargs.len()..].to_vec();
        if js.iter().any(|j| contains_const(j, ind)) {
            return kerr(format!("`{ind}` may not occur in its own indices"));
        }
        Ok(Some((xs, js)))
    }
}

impl Env {
    pub fn add_inductive(&mut self, d: InductiveDecl) -> KResult<()> {
        let backup = self.clone();
        let r = self.add_inductive_inner(d);
        if r.is_err() {
            *self = backup;
        }
        r
    }

    fn add_inductive_inner(&mut self, d: InductiveDecl) -> KResult<()> {
        self.check_fresh(&d.name)?;
        let rec_name: Name = format!("{}.rec", d.name).into();
        self.check_fresh(&rec_name)?;
        for (c, _) in &d.ctors {
            self.check_fresh(c)?;
        }
        let mut level_terms: Vec<&T> = vec![&d.ty];
        level_terms.extend(d.ctors.iter().map(|(_, t)| t));
        self.check_decl_levels(&d.lparams, &level_terms)?;

        // the inductive type itself
        let (ind_level, nindices) = {
            let mut tc = TypeChecker::new(self);
            tc.check_is_type(&d.ty)?;
            let (fvs, res) = tc.telescope(&d.ty, None)?;
            if fvs.len() < d.nparams {
                return kerr("inductive type has fewer binders than parameters");
            }
            match &*res {
                Term::Sort(l) => (l.clone(), fvs.len() - d.nparams),
                _ => return kerr("the type of an inductive type must end in a Sort"),
            }
        };
        let is_prop = ind_level.is_zero();
        let ctor_names: Vec<Name> = d.ctors.iter().map(|(n, _)| n.clone()).collect();
        let mut tmp = self.clone();
        tmp.insert(
            d.name.clone(),
            Decl::Inductive(IndInfo {
                lparams: d.lparams.clone(),
                ty: d.ty.clone(),
                nparams: d.nparams,
                nindices,
                ctors: ctor_names.clone(),
                is_prop,
                rec: rec_name.clone(),
            }),
        );

        let ind_levels: Vec<Level> = d.lparams.iter().map(|p| Level::Param(p.clone())).collect();
        let mut tc = TypeChecker::new(&tmp);
        let (pfv, rest_ty) = tc.telescope(&d.ty, Some(d.nparams))?;
        let pargs: Vec<T> = pfv.iter().map(|&i| fvar(i)).collect();
        let (ifv, _) = tc.telescope(&rest_ty, None)?;
        let iargs: Vec<T> = ifv.iter().map(|&i| fvar(i)).collect();
        let ind_const = cnst(d.name.clone(), ind_levels.clone());

        // constructors
        let mut analyses: Vec<CtorAnalysis> = Vec::new();
        for (cname, cty) in &d.ctors {
            tc.check_is_type(cty)?;
            let rest = tc.instantiate_pis(cty, &pargs)?;
            let (fields, res) = tc.telescope(&rest, None)?;
            let (head, rargs) = app_spine(&res);
            let returns_ind =
                matches!(&*head, Term::Const(n, ls) if *n == d.name && *ls == ind_levels);
            if !returns_ind || rargs.len() != d.nparams + nindices {
                return kerr(format!(
                    "constructor `{cname}` must return `{}` applied to its parameters and indices",
                    d.name
                ));
            }
            if rargs[..d.nparams] != *pargs {
                return kerr(format!(
                    "constructor `{cname}` must use the inductive's parameters unchanged"
                ));
            }
            let res_indices = rargs[d.nparams..].to_vec();
            if res_indices.iter().any(|ix| contains_const(ix, &d.name)) {
                return kerr(format!(
                    "constructor `{cname}`: `{}` may not occur in its own indices",
                    d.name
                ));
            }
            let mut recs = Vec::new();
            let mut field_is_prop = Vec::new();
            for &f in &fields {
                let fty = tc.local_ty(f)?;
                let lvl = tc.check_is_type(&fty)?;
                if !is_prop && !lvl.leq(&ind_level) {
                    return kerr(format!(
                        "universe level of a field in constructor `{cname}` is too large for `{}`",
                        d.name
                    ));
                }
                field_is_prop.push(lvl.is_zero());
                recs.push(tc.analyze_rec_field(&fty, &d.name, &ind_levels, &pargs)?);
            }
            analyses.push(CtorAnalysis {
                fields,
                recs,
                res_indices,
                field_is_prop,
            });
        }

        // large elimination: a Prop may eliminate into any Sort only if it is
        // a subsingleton (no constructors, or one whose fields are props or indices)
        let large = !is_prop
            || analyses.is_empty()
            || (analyses.len() == 1 && {
                let a = &analyses[0];
                (0..a.fields.len()).all(|j| {
                    a.field_is_prop[j]
                        || a.res_indices
                            .iter()
                            .any(|ix| contains_fvar(ix, a.fields[j]))
                })
            });

        // recursor
        let mut u_name = String::from("u");
        while d.lparams.iter().any(|p| **p == *u_name) {
            u_name.push('\'');
        }
        let u_name: Name = u_name.into();
        let elim = if large {
            Level::Param(u_name.clone())
        } else {
            Level::Zero
        };
        let mut rec_lparams = d.lparams.clone();
        if large {
            rec_lparams.insert(0, u_name.clone());
        }
        let rec_levels: Vec<Level> = rec_lparams
            .iter()
            .map(|p| Level::Param(p.clone()))
            .collect();

        let major_ty = mk_apps(&ind_const, &[pargs.clone(), iargs.clone()].concat());
        let major = tc.fresh("t", major_ty, Mult::Omega);
        let motive_ty = tc.mk_pi(&[ifv.clone(), vec![major]].concat(), &sort(elim));
        let motive = tc.fresh("motive", motive_ty, Mult::Omega);
        let motive_t = fvar(motive);

        let mut minors = Vec::new();
        for (ci, (cname, _)) in d.ctors.iter().enumerate() {
            let a = &analyses[ci];
            let field_args: Vec<T> = a.fields.iter().map(|&f| fvar(f)).collect();
            let ctor_app = mk_apps(
                &cnst(cname.clone(), ind_levels.clone()),
                &[pargs.clone(), field_args].concat(),
            );
            let mut ihs = Vec::new();
            for (j, r) in a.recs.iter().enumerate() {
                if let Some((xs, js)) = r {
                    let xargs: Vec<T> = xs.iter().map(|&x| fvar(x)).collect();
                    let applied = mk_apps(&fvar(a.fields[j]), &xargs);
                    let body = mk_apps(&motive_t, &[js.clone(), vec![applied]].concat());
                    let ih_ty = tc.mk_pi(xs, &body);
                    ihs.push(tc.fresh("ih", ih_ty, Mult::Omega));
                }
            }
            let concl = mk_apps(&motive_t, &[a.res_indices.clone(), vec![ctor_app]].concat());
            let minor_ty = tc.mk_pi(&[a.fields.clone(), ihs].concat(), &concl);
            minors.push(tc.fresh(cname, minor_ty, Mult::Omega));
        }

        let rec_binders = [
            pfv.clone(),
            vec![motive],
            minors.clone(),
            ifv.clone(),
            vec![major],
        ]
        .concat();
        let rec_ty = tc.mk_pi(
            &rec_binders,
            &mk_apps(&motive_t, &[iargs.clone(), vec![fvar(major)]].concat()),
        );

        let rec_const = cnst(rec_name.clone(), rec_levels);
        let minor_args: Vec<T> = minors.iter().map(|&m| fvar(m)).collect();
        let mut rules = Vec::new();
        for (ci, (cname, _)) in d.ctors.iter().enumerate() {
            let a = &analyses[ci];
            let field_args: Vec<T> = a.fields.iter().map(|&f| fvar(f)).collect();
            let mut ih_vals = Vec::new();
            for (j, r) in a.recs.iter().enumerate() {
                if let Some((xs, js)) = r {
                    let xargs: Vec<T> = xs.iter().map(|&x| fvar(x)).collect();
                    let applied = mk_apps(&fvar(a.fields[j]), &xargs);
                    let rec_app = mk_apps(
                        &rec_const,
                        &[
                            pargs.clone(),
                            vec![motive_t.clone()],
                            minor_args.clone(),
                            js.clone(),
                            vec![applied],
                        ]
                        .concat(),
                    );
                    ih_vals.push(tc.mk_lam(xs, &rec_app));
                }
            }
            let body = mk_apps(&fvar(minors[ci]), &[field_args, ih_vals].concat());
            let rhs = tc.mk_lam(
                &[pfv.clone(), vec![motive], minors.clone(), a.fields.clone()].concat(),
                &body,
            );
            rules.push(RecRule {
                ctor: cname.clone(),
                nfields: a.fields.len(),
                rhs,
            });
        }

        let nminors = d.ctors.len();
        let ctor_infos: Vec<(Name, CtorInfo)> = d
            .ctors
            .iter()
            .enumerate()
            .map(|(i, (n, t))| {
                let info = CtorInfo {
                    lparams: d.lparams.clone(),
                    ty: t.clone(),
                    ind: d.name.clone(),
                    idx: i,
                    nparams: d.nparams,
                    nfields: analyses[i].fields.len(),
                };
                (n.clone(), info)
            })
            .collect();

        self.insert(
            d.name.clone(),
            Decl::Inductive(IndInfo {
                lparams: d.lparams.clone(),
                ty: d.ty.clone(),
                nparams: d.nparams,
                nindices,
                ctors: ctor_names,
                is_prop,
                rec: rec_name.clone(),
            }),
        );
        for (n, info) in ctor_infos {
            self.insert(n, Decl::Ctor(info));
        }
        self.insert(
            rec_name,
            Decl::Rec(RecInfo {
                lparams: rec_lparams,
                ty: rec_ty,
                ind: d.name.clone(),
                nparams: d.nparams,
                nindices,
                nminors,
                rules,
            }),
        );
        Ok(())
    }
}
