//! Nested inductive types: `enum Rose { Node(Nat, List<Rose>) }`.
//!
//! As in Lean, a field of type `J args` (an existing inductive type applied to arguments that
//! mention the family being defined) is handled by an *auxiliary type*: a copy `A` of `J args`
//! (its constructors are `J`'s, with `args` substituted) that joins the mutual family. The
//! mutual machinery generates the recursors for the extended family; then every mention of an
//! auxiliary type or constructor is translated back (`A ↦ J args`, `A.c ↦ J.c args`), so the
//! declared types, the recursors and their reduction rules talk about the real `J`. The
//! translated recursors are re-checked by the type checker before they are accepted.

use crate::env::*;
use crate::inductive::*;
use crate::level::Level;
use crate::tc::TypeChecker;
use crate::term::*;

/// An auxiliary type standing for `ind args`.
pub(crate) struct Aux {
    name: Name,
    ind: Name,
    levels: Vec<Level>,
    /// The parameters of `ind`, abstracted over the family's parameters.
    args_abs: Vec<T>,
    /// (auxiliary constructor, constructor of `ind`)
    ctors: Vec<(Name, Name)>,
}

/// Replace `J jargs` (a spine with exactly these leading arguments) by `to`.
fn replace_spine(t: &T, j: &Name, jl: &[Level], jargs: &[T], to: &T) -> T {
    match &**t {
        Term::App(..) => {
            let (h, args) = app_spine(t);
            if let Term::Const(n, ls) = &*h {
                if n == j
                    && ls.as_slice() == jl
                    && args.len() >= jargs.len()
                    && args[..jargs.len()] == *jargs
                {
                    return mk_apps(to, &args[jargs.len()..]);
                }
            }
            let args: Vec<T> = args
                .iter()
                .map(|a| replace_spine(a, j, jl, jargs, to))
                .collect();
            mk_apps(&replace_spine(&h, j, jl, jargs, to), &args)
        }
        Term::Lam(m, ty, b) => lam(
            *m,
            replace_spine(ty, j, jl, jargs, to),
            replace_spine(b, j, jl, jargs, to),
        ),
        Term::Pi(m, ty, b) => pi(
            *m,
            replace_spine(ty, j, jl, jargs, to),
            replace_spine(b, j, jl, jargs, to),
        ),
        Term::Const(n, ls) if n == j && ls.as_slice() == jl && jargs.is_empty() => to.clone(),
        _ => t.clone(),
    }
}

fn mentions_any(t: &T, names: &[Name]) -> bool {
    names.iter().any(|n| contains_const(t, n))
}

impl Env {
    /// Find nested occurrences in the constructors of `d` and extend the family with
    /// auxiliary types. `None` if there are none.
    pub(crate) fn expand_nested(&self, d: &MutualDecl) -> KResult<Option<(MutualDecl, Vec<Aux>)>> {
        let fam: Vec<Name> = d.types.iter().map(|t| t.name.clone()).collect();
        let mut tmp = self.clone();
        for t in &d.types {
            tmp.insert(
                t.name.clone(),
                Decl::Axiom {
                    lparams: d.lparams.clone(),
                    ty: t.ty.clone(),
                },
            );
        }
        let mut tc = TypeChecker::new(&tmp);
        let (pfv, _) = tc.telescope(&d.types[0].ty, Some(d.nparams))?;
        let pargs: Vec<T> = pfv.iter().map(|&i| fvar(i)).collect();
        let (_, res_sort) = tc.telescope(&d.types[0].ty, None)?;
        let Term::Sort(level) = &*res_sort else {
            return Ok(None); // reported properly by the checks of the plain path
        };
        let ind_levels: Vec<Level> = d.lparams.iter().map(|p| Level::Param(p.clone())).collect();
        let mut types: Vec<TypeDecl> = d
            .types
            .iter()
            .map(|t| TypeDecl {
                name: t.name.clone(),
                ty: t.ty.clone(),
                ctors: t.ctors.clone(),
            })
            .collect();
        let mut auxes: Vec<Aux> = Vec::new();
        let mut ti = 0;
        while ti < types.len() {
            let mut ci = 0;
            while ci < types[ti].ctors.len() {
                let cty = types[ti].ctors[ci].1.clone();
                let rest = tc.instantiate_pis(&cty, &pargs)?;
                let (fields, res) = tc.telescope(&rest, None)?;
                let mut changed = false;
                let mut new_tys: Vec<T> = Vec::new();
                for &f in &fields {
                    let fty = tc.local_ty(f)?;
                    let (xs, r) = tc.telescope(&fty, None)?;
                    let (h, args) = app_spine(&r);
                    let names: Vec<Name> = fam
                        .iter()
                        .cloned()
                        .chain(auxes.iter().map(|a| a.name.clone()))
                        .chain(types[d.types.len()..].iter().map(|t| t.name.clone()))
                        .collect();
                    let nested = match &*h {
                        Term::Const(jn, jl) if !names.contains(jn) => match tmp.get(jn) {
                            Some(Decl::Inductive(ji)) => {
                                let jp = ji.nparams;
                                if args.len() >= jp
                                    && args[..jp].iter().any(|a| mentions_any(a, &names))
                                {
                                    Some((jn.clone(), jl.clone(), ji.clone(), args))
                                } else {
                                    None
                                }
                            }
                            _ => None,
                        },
                        _ => None,
                    };
                    let Some((jn, jl, ji, args)) = nested else {
                        new_tys.push(fty);
                        continue;
                    };
                    if ji.nindices > 0 || args.len() != ji.nparams {
                        return kerr(format!(
                            "a nested occurrence of the indexed family `{jn}` is not supported"
                        ));
                    }
                    if !xs.is_empty() {
                        return kerr("a nested occurrence under a function arrow is not supported");
                    }
                    let jargs = args;
                    // an auxiliary type for `jn jargs`, made once
                    let key: Vec<T> = jargs.iter().map(|a| abstract_fvars(a, &pfv)).collect();
                    let idx = match auxes
                        .iter()
                        .position(|a| a.ind == jn && a.levels == jl && a.args_abs == key)
                    {
                        Some(i) => i,
                        None => {
                            let aname: Name =
                                format!("{}._nested{}", fam[0], auxes.len() + 1).into();
                            let a_app = mk_apps(&cnst(aname.clone(), ind_levels.clone()), &pargs);
                            let mut ctors = Vec::new();
                            let mut decl_ctors = Vec::new();
                            for jc in &ji.ctors {
                                let jcty = tmp.const_type(jc, &jl)?;
                                let body = tc.instantiate_pis(&jcty, &jargs)?;
                                let body = replace_spine(&body, &jn, &jl, &jargs, &a_app);
                                let short = jc.rsplit('.').next().unwrap_or(jc);
                                let acn: Name = format!("{aname}.{short}").into();
                                decl_ctors.push((acn.clone(), tc.mk_pi(&pfv, &body)));
                                ctors.push((acn, jc.clone()));
                            }
                            types.push(TypeDecl {
                                name: aname.clone(),
                                ty: tc.mk_pi(&pfv, &sort(level.clone())),
                                ctors: decl_ctors,
                            });
                            auxes.push(Aux {
                                name: aname,
                                ind: jn.clone(),
                                levels: jl.clone(),
                                args_abs: key,
                                ctors,
                            });
                            auxes.len() - 1
                        }
                    };
                    changed = true;
                    new_tys.push(mk_apps(
                        &cnst(auxes[idx].name.clone(), ind_levels.clone()),
                        &pargs,
                    ));
                }
                if changed {
                    // rebuild the constructor type with the new field types
                    let all: Vec<u32> = pfv.iter().chain(&fields).copied().collect();
                    let mut tys: Vec<T> = pfv
                        .iter()
                        .map(|&p| tc.local_ty(p))
                        .collect::<KResult<_>>()?;
                    tys.extend(new_tys);
                    let mut r = abstract_fvars(&res, &all);
                    for i in (0..all.len()).rev() {
                        let ty = abstract_fvars(&tys[i], &all[..i]);
                        let m = tc.local_mult(all[i]).unwrap_or(Mult::Omega);
                        r = pi(m, ty, r);
                    }
                    types[ti].ctors[ci].1 = r;
                }
                ci += 1;
            }
            ti += 1;
        }
        if auxes.is_empty() {
            return Ok(None);
        }
        Ok(Some((
            MutualDecl {
                lparams: d.lparams.clone(),
                nparams: d.nparams,
                types,
            },
            auxes,
        )))
    }

    /// Translate auxiliary types and constructors back to the nested types they stand for.
    fn restore_nested(t: &T, auxes: &[Aux], np: usize) -> T {
        match &**t {
            Term::App(..) | Term::Const(..) => {
                let (h, args) = app_spine(t);
                let args: Vec<T> = args
                    .iter()
                    .map(|a| Self::restore_nested(a, auxes, np))
                    .collect();
                if let Term::Const(n, _) = &*h {
                    for a in auxes {
                        let head = if *n == a.name {
                            Some(a.ind.clone())
                        } else {
                            a.ctors.iter().find(|(c, _)| c == n).map(|(_, j)| j.clone())
                        };
                        if let Some(target) = head {
                            if args.len() >= np {
                                let jargs: Vec<T> = a
                                    .args_abs
                                    .iter()
                                    .map(|x| instantiate_many(x, &args[..np]))
                                    .collect();
                                let base = mk_apps(&cnst(target, a.levels.clone()), &jargs);
                                return mk_apps(&base, &args[np..]);
                            }
                        }
                    }
                }
                mk_apps(&h, &args)
            }
            Term::Lam(m, ty, b) => lam(
                *m,
                Self::restore_nested(ty, auxes, np),
                Self::restore_nested(b, auxes, np),
            ),
            Term::Pi(m, ty, b) => pi(
                *m,
                Self::restore_nested(ty, auxes, np),
                Self::restore_nested(b, auxes, np),
            ),
            Term::Let(m, ty, v, b) => let_(
                *m,
                Self::restore_nested(ty, auxes, np),
                Self::restore_nested(v, auxes, np),
                Self::restore_nested(b, auxes, np),
            ),
            _ => t.clone(),
        }
    }

    /// Add the extended family on a scratch copy, then keep the translated results.
    pub(crate) fn add_nested(
        &mut self,
        orig: MutualDecl,
        ext: MutualDecl,
        auxes: Vec<Aux>,
    ) -> KResult<()> {
        let np = orig.nparams;
        let mut scratch = self.clone();
        scratch.add_mutual_inner(ext)?;
        let fam: Vec<Name> = orig.types.iter().map(|t| t.name.clone()).collect();
        let nested: Vec<NestedInfo> = auxes
            .iter()
            .map(|a| NestedInfo {
                rec: format!("{}.rec", a.name).into(),
                ind: a.ind.clone(),
                levels: a.levels.clone(),
                args: a.args_abs.clone(),
                ctors: a.ctors.iter().map(|(_, j)| j.clone()).collect(),
            })
            .collect();
        let fix_rec = |ri: &RecInfo, ind: Name| -> RecInfo {
            RecInfo {
                lparams: ri.lparams.clone(),
                ty: Self::restore_nested(&ri.ty, &auxes, np),
                ind,
                nparams: ri.nparams,
                nindices: ri.nindices,
                nmotives: ri.nmotives,
                nminors: ri.nminors,
                rules: ri
                    .rules
                    .iter()
                    .map(|ru| RecRule {
                        ctor: auxes
                            .iter()
                            .find_map(|a| {
                                a.ctors
                                    .iter()
                                    .find(|(c, _)| *c == ru.ctor)
                                    .map(|(_, j)| j.clone())
                            })
                            .unwrap_or_else(|| ru.ctor.clone()),
                        nfields: ru.nfields,
                        rhs: Self::restore_nested(&ru.rhs, &auxes, np),
                    })
                    .collect(),
            }
        };
        let mut new_recs: Vec<(Name, RecInfo)> = Vec::new();
        for t in &orig.types {
            let Some(Decl::Inductive(ii)) = scratch.get(&t.name).cloned() else {
                return kerr("internal error: nested family was not added");
            };
            self.insert(
                t.name.clone(),
                Decl::Inductive(IndInfo {
                    family: fam.clone(),
                    nested: nested.clone(),
                    ..ii.clone()
                }),
            );
            for (cn, cty) in &t.ctors {
                let Some(Decl::Ctor(ci)) = scratch.get(cn).cloned() else {
                    return kerr("internal error: missing constructor");
                };
                self.insert(
                    cn.clone(),
                    Decl::Ctor(CtorInfo {
                        ty: cty.clone(),
                        ..ci
                    }),
                );
            }
            let Some(Decl::Rec(ri)) = scratch.get(&ii.rec).cloned() else {
                return kerr("internal error: missing recursor");
            };
            new_recs.push((ii.rec.clone(), fix_rec(&ri, t.name.clone())));
        }
        for a in &auxes {
            let rn: Name = format!("{}.rec", a.name).into();
            let Some(Decl::Rec(ri)) = scratch.get(&rn).cloned() else {
                return kerr("internal error: missing auxiliary recursor");
            };
            new_recs.push((rn, fix_rec(&ri, a.ind.clone())));
        }
        for (n, r) in &new_recs {
            self.insert(n.clone(), Decl::Rec(r.clone()));
        }
        // the translation is not trusted: the recursors must type check as they stand
        for (n, r) in &new_recs {
            let mut tc = TypeChecker::new(self);
            tc.check_is_type(&r.ty)
                .map_err(|e| KernelError(format!("nested recursor `{n}`: {e}")))?;
            for ru in &r.rules {
                tc.infer(&ru.rhs)
                    .map_err(|e| KernelError(format!("nested recursor `{n}`: {e}")))?;
            }
        }
        Ok(())
    }
}
