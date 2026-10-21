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

/// One type of a mutual family.
pub struct TypeDecl {
    pub name: Name,
    pub ty: T,
    pub ctors: Vec<(Name, T)>,
}

/// Mutually inductive types sharing universe parameters and parameters.
pub struct MutualDecl {
    pub lparams: Vec<Name>,
    pub nparams: usize,
    pub types: Vec<TypeDecl>,
}

/// A recursive field `Π xs, I_j params js`: (xs, js, j).
type RecField = (Vec<u32>, Vec<T>, usize);

struct CtorAnalysis {
    fields: Vec<u32>,
    /// Per field: `Some((xs, js, j))` if recursive — `Π xs, I_j params js`.
    recs: Vec<Option<RecField>>,
    res_indices: Vec<T>,
    field_is_prop: Vec<bool>,
}

impl<'a> TypeChecker<'a> {
    fn analyze_rec_field(
        &mut self,
        fty: &T,
        inds: &[Name],
        levels: &[Level],
        pargs: &[T],
    ) -> KResult<Option<RecField>> {
        if !inds.iter().any(|n| contains_const(fty, n)) {
            return Ok(None);
        }
        let (xs, res) = self.telescope(fty, None)?;
        for &x in &xs {
            if let Some(n) = inds
                .iter()
                .find(|n| contains_const(&self.local_ty(x).unwrap(), n))
            {
                return kerr(format!(
                    "non-positive occurrence of `{n}` (strict positivity violation)"
                ));
            }
        }
        let (head, args) = app_spine(&res);
        let which = match &*head {
            Term::Const(n, ls) if *ls == levels => inds.iter().position(|m| m == n),
            _ => None,
        };
        let Some(j) = which.filter(|_| args.len() >= pargs.len()) else {
            return kerr(format!(
                "invalid occurrence of `{}` in constructor field",
                inds[0]
            ));
        };
        if args[..pargs.len()] != *pargs {
            return kerr(format!(
                "recursive occurrence of `{}` must use the same parameters",
                inds[j]
            ));
        }
        let js = args[pargs.len()..].to_vec();
        if js
            .iter()
            .any(|jx| inds.iter().any(|n| contains_const(jx, n)))
        {
            return kerr(format!("`{}` may not occur in its own indices", inds[j]));
        }
        Ok(Some((xs, js, j)))
    }
}

impl Env {
    pub fn add_inductive(&mut self, d: InductiveDecl) -> KResult<()> {
        self.add_mutual(MutualDecl {
            lparams: d.lparams,
            nparams: d.nparams,
            types: vec![TypeDecl {
                name: d.name,
                ty: d.ty,
                ctors: d.ctors,
            }],
        })
    }

    /// Add mutually inductive types together with their recursors.
    pub fn add_mutual(&mut self, d: MutualDecl) -> KResult<()> {
        let backup = self.clone();
        let r = match self.expand_nested(&d) {
            Err(e) => Err(e),
            Ok(None) => self.add_mutual_inner(d),
            Ok(Some((ext, auxes))) => self.add_nested(d, ext, auxes),
        };
        if r.is_err() {
            *self = backup;
        }
        r
    }

    pub(crate) fn add_mutual_inner(&mut self, d: MutualDecl) -> KResult<()> {
        if d.types.is_empty() {
            return kerr("an inductive declaration needs at least one type");
        }
        let n = d.types.len();
        let rec_names: Vec<Name> = d
            .types
            .iter()
            .map(|t| format!("{}.rec", t.name).into())
            .collect();
        for (i, t) in d.types.iter().enumerate() {
            self.check_fresh(&t.name)?;
            self.check_fresh(&rec_names[i])?;
            for (c, _) in &t.ctors {
                self.check_fresh(c)?;
            }
        }
        let mut level_terms: Vec<&T> = Vec::new();
        for t in &d.types {
            level_terms.push(&t.ty);
            level_terms.extend(t.ctors.iter().map(|(_, c)| c));
        }
        self.check_decl_levels(&d.lparams, &level_terms)?;

        // the types themselves
        let mut ind_level: Option<Level> = None;
        let mut nindices_of = Vec::new();
        for t in &d.types {
            let mut tc = TypeChecker::new(self);
            tc.check_is_type(&t.ty)?;
            let (fvs, res) = tc.telescope(&t.ty, None)?;
            if fvs.len() < d.nparams {
                return kerr("inductive type has fewer binders than parameters");
            }
            match &*res {
                Term::Sort(l) => {
                    match &ind_level {
                        Some(first) if !first.equiv(l) => {
                            return kerr("mutually inductive types must live in the same universe")
                        }
                        _ => ind_level = Some(l.clone()),
                    }
                    nindices_of.push(fvs.len() - d.nparams);
                }
                _ => return kerr("the type of an inductive type must end in a Sort"),
            }
        }
        let ind_level = ind_level.expect("at least one type");
        let is_prop = ind_level.is_zero();
        let ctor_names: Vec<Vec<Name>> = d
            .types
            .iter()
            .map(|t| t.ctors.iter().map(|(c, _)| c.clone()).collect())
            .collect();
        let mut tmp = self.clone();
        for (k, t) in d.types.iter().enumerate() {
            tmp.insert(
                t.name.clone(),
                Decl::Inductive(IndInfo {
                    lparams: d.lparams.clone(),
                    ty: t.ty.clone(),
                    nparams: d.nparams,
                    nindices: nindices_of[k],
                    ctors: ctor_names[k].clone(),
                    is_prop,
                    rec: rec_names[k].clone(),
                    family: d.types.iter().map(|t| t.name.clone()).collect(),
                    nested: vec![],
                }),
            );
        }

        let ind_levels: Vec<Level> = d.lparams.iter().map(|p| Level::Param(p.clone())).collect();
        let inds: Vec<Name> = d.types.iter().map(|t| t.name.clone()).collect();
        let mut tc = TypeChecker::new(&tmp);
        let (pfv, _) = tc.telescope(&d.types[0].ty, Some(d.nparams))?;
        let pargs: Vec<T> = pfv.iter().map(|&i| fvar(i)).collect();

        // per type: index telescope
        let mut ifvs: Vec<Vec<u32>> = Vec::new();
        for t in &d.types {
            let rest_ty = tc.instantiate_pis(&t.ty, &pargs)?;
            let (ifv, _) = tc.telescope(&rest_ty, None)?;
            ifvs.push(ifv);
        }

        // constructors, per type
        let mut analyses: Vec<Vec<CtorAnalysis>> = Vec::new();
        for (k, t) in d.types.iter().enumerate() {
            let mut an = Vec::new();
            for (cname, cty) in &t.ctors {
                tc.check_is_type(cty)?;
                let rest = tc.instantiate_pis(cty, &pargs)?;
                let (fields, res) = tc.telescope(&rest, None)?;
                let (head, rargs) = app_spine(&res);
                let returns_ind =
                    matches!(&*head, Term::Const(m, ls) if *m == t.name && *ls == ind_levels);
                if !returns_ind || rargs.len() != d.nparams + nindices_of[k] {
                    return kerr(format!(
                        "constructor `{cname}` must return `{}` applied to its parameters and indices",
                        t.name
                    ));
                }
                if rargs[..d.nparams] != *pargs {
                    return kerr(format!(
                        "constructor `{cname}` must use the inductive's parameters unchanged"
                    ));
                }
                let res_indices = rargs[d.nparams..].to_vec();
                if res_indices
                    .iter()
                    .any(|ix| inds.iter().any(|m| contains_const(ix, m)))
                {
                    return kerr(format!(
                        "constructor `{cname}`: `{}` may not occur in its own indices",
                        t.name
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
                            t.name
                        ));
                    }
                    field_is_prop.push(lvl.is_zero());
                    recs.push(tc.analyze_rec_field(&fty, &inds, &ind_levels, &pargs)?);
                }
                an.push(CtorAnalysis {
                    fields,
                    recs,
                    res_indices,
                    field_is_prop,
                });
            }
            analyses.push(an);
        }

        // large elimination: a Prop may eliminate into any Sort only if it is a
        // single subsingleton type (no constructors, or one whose fields are
        // props or indices)
        let large = !is_prop
            || (n == 1
                && (analyses[0].is_empty()
                    || (analyses[0].len() == 1 && {
                        let a = &analyses[0][0];
                        (0..a.fields.len()).all(|j| {
                            a.field_is_prop[j]
                                || a.res_indices
                                    .iter()
                                    .any(|ix| contains_fvar(ix, a.fields[j]))
                        })
                    })));

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

        // one motive per type
        let mut majors = Vec::new();
        let mut motives = Vec::new();
        for (k, t) in d.types.iter().enumerate() {
            let iargs: Vec<T> = ifvs[k].iter().map(|&i| fvar(i)).collect();
            let major_ty = mk_apps(
                &cnst(t.name.clone(), ind_levels.clone()),
                &[pargs.clone(), iargs].concat(),
            );
            let major = tc.fresh("t", major_ty, Mult::Omega);
            let motive_ty = tc.mk_pi(
                &[ifvs[k].clone(), vec![major]].concat(),
                &sort(elim.clone()),
            );
            let motive = tc.fresh(&format!("motive_{}", k + 1), motive_ty, Mult::Zero);
            majors.push(major);
            motives.push(motive);
        }

        // one minor premise per constructor, in declaration order
        let mut minors = Vec::new();
        for (k, t) in d.types.iter().enumerate() {
            for (ci, (cname, _)) in t.ctors.iter().enumerate() {
                let a = &analyses[k][ci];
                let field_args: Vec<T> = a.fields.iter().map(|&f| fvar(f)).collect();
                let ctor_app = mk_apps(
                    &cnst(cname.clone(), ind_levels.clone()),
                    &[pargs.clone(), field_args].concat(),
                );
                let mut ihs = Vec::new();
                for (j, r) in a.recs.iter().enumerate() {
                    if let Some((xs, js, which)) = r {
                        let xargs: Vec<T> = xs.iter().map(|&x| fvar(x)).collect();
                        let applied = mk_apps(&fvar(a.fields[j]), &xargs);
                        let body = mk_apps(
                            &fvar(motives[*which]),
                            &[js.clone(), vec![applied]].concat(),
                        );
                        let ih_ty = tc.mk_pi(xs, &body);
                        ihs.push(tc.fresh("ih", ih_ty, Mult::Omega));
                    }
                }
                let concl = mk_apps(
                    &fvar(motives[k]),
                    &[a.res_indices.clone(), vec![ctor_app]].concat(),
                );
                let minor_ty = tc.mk_pi(&[a.fields.clone(), ihs].concat(), &concl);
                minors.push(tc.fresh(cname, minor_ty, Mult::Omega));
            }
        }
        let minor_args: Vec<T> = minors.iter().map(|&m| fvar(m)).collect();
        let motive_args: Vec<T> = motives.iter().map(|&m| fvar(m)).collect();
        let rec_consts: Vec<T> = rec_names
            .iter()
            .map(|r| cnst(r.clone(), rec_levels.clone()))
            .collect();

        let mut rec_decls = Vec::new();
        let mut offset = 0;
        for (k, t) in d.types.iter().enumerate() {
            let iargs: Vec<T> = ifvs[k].iter().map(|&i| fvar(i)).collect();
            let rec_binders = [
                pfv.clone(),
                motives.clone(),
                minors.clone(),
                ifvs[k].clone(),
                vec![majors[k]],
            ]
            .concat();
            let rec_ty = tc.mk_pi(
                &rec_binders,
                &mk_apps(&fvar(motives[k]), &[iargs, vec![fvar(majors[k])]].concat()),
            );
            let mut rules = Vec::new();
            for (ci, (cname, _)) in t.ctors.iter().enumerate() {
                let a = &analyses[k][ci];
                let field_args: Vec<T> = a.fields.iter().map(|&f| fvar(f)).collect();
                let mut ih_vals = Vec::new();
                for (j, r) in a.recs.iter().enumerate() {
                    if let Some((xs, js, which)) = r {
                        let xargs: Vec<T> = xs.iter().map(|&x| fvar(x)).collect();
                        let applied = mk_apps(&fvar(a.fields[j]), &xargs);
                        let rec_app = mk_apps(
                            &rec_consts[*which],
                            &[
                                pargs.clone(),
                                motive_args.clone(),
                                minor_args.clone(),
                                js.clone(),
                                vec![applied],
                            ]
                            .concat(),
                        );
                        ih_vals.push(tc.mk_lam(xs, &rec_app));
                    }
                }
                let body = mk_apps(&fvar(minors[offset + ci]), &[field_args, ih_vals].concat());
                let rhs = tc.mk_lam(
                    &[
                        pfv.clone(),
                        motives.clone(),
                        minors.clone(),
                        a.fields.clone(),
                    ]
                    .concat(),
                    &body,
                );
                rules.push(RecRule {
                    ctor: cname.clone(),
                    nfields: a.fields.len(),
                    rhs,
                });
            }
            offset += t.ctors.len();
            rec_decls.push(Decl::Rec(RecInfo {
                lparams: rec_lparams.clone(),
                ty: rec_ty,
                ind: t.name.clone(),
                nparams: d.nparams,
                nindices: nindices_of[k],
                nmotives: n,
                nminors: minors.len(),
                rules,
            }));
        }

        for (k, t) in d.types.iter().enumerate() {
            self.insert(
                t.name.clone(),
                Decl::Inductive(IndInfo {
                    lparams: d.lparams.clone(),
                    ty: t.ty.clone(),
                    nparams: d.nparams,
                    nindices: nindices_of[k],
                    ctors: ctor_names[k].clone(),
                    is_prop,
                    rec: rec_names[k].clone(),
                    family: d.types.iter().map(|t| t.name.clone()).collect(),
                    nested: vec![],
                }),
            );
            for (ci, (cn, cty)) in t.ctors.iter().enumerate() {
                self.insert(
                    cn.clone(),
                    Decl::Ctor(CtorInfo {
                        lparams: d.lparams.clone(),
                        ty: cty.clone(),
                        ind: t.name.clone(),
                        idx: ci,
                        nparams: d.nparams,
                        nfields: analyses[k][ci].fields.len(),
                    }),
                );
            }
        }
        for (k, rd) in rec_decls.into_iter().enumerate() {
            self.insert(rec_names[k].clone(), rd);
        }
        if n == 1 && d.types.len() == 1 {
            self.add_below_brec(&d.types[0].name)?;
        }
        Ok(())
    }
}
