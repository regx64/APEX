//! Mutually structural recursion over a mutual family of enums:
//!
//! ```text
//! mutual {
//!     fn size_tree<T>(t: Tree<T>) -> Nat { match t { Tree.Node(_, f) => 1 + size_forest(f) } }
//!     fn size_forest<T>(f: Forest<T>) -> Nat { match f { Forest.Nil => 0, Forest.Cons(t, r) => size_tree(t) + size_forest(r) } }
//! }
//! ```
//!
//! There is one function per type of the family, each decreasing on its first
//! parameter (whose type arguments are the function's type parameters), with the
//! rest of the parameters free. They are all defined through the family's shared
//! recursor: the motive of the type `K` is `fun t => Π others, result` of its
//! function, a call of any function of the group on a field becomes the induction
//! hypothesis of that field, and the minor premises, one per constructor, come from
//! the `match` of the function for the constructor's type.

use super::*;

/// A function of the group, after its signature was elaborated.
struct Member<'a> {
    cx: Cx<'a>,
    f: &'a FnDecl,
    fvs: Vec<u32>,
    mask: Vec<Bk>,
    ngen: usize,
    x: u32,
    explicit: Vec<u32>,
    ret: T,
    iname: String,
    ilevels: Vec<Level>,
    /// The family's parameters, as this function's first parameter instantiates them.
    params: Vec<T>,
    /// The slot in the family (its types, then the nested occurrences) and the family's
    /// parameters as seen from this function.
    slot: usize,
    fam_params: Vec<T>,
    lvl: Level,
    /// `fun gens => fun t => Π others, result`
    motive: T,
}

impl Elaborator {
    pub(super) fn elab_mutual_fns(&mut self, fs: &[&FnDecl], span: Span) -> R<()> {
        let results = self.try_mutual_fns(fs, span)?;
        for (f, (ty, val, mask)) in fs.iter().zip(results) {
            let callee = callee_of(f, &[]).map_err(sig_error)?;
            let qname = self.qualified(&f.name);
            let kname = self.add_def_named(&qname, ty, val, mask)?;
            self.tables.sigs.insert(kname, callee);
        }
        Ok(())
    }

    fn try_mutual_fns(&self, fs: &[&FnDecl], span: Span) -> R<Vec<(T, T, Vec<Bk>)>> {
        // ---- phase A: signatures and motives ----
        let mut ms: Vec<Member> = Vec::new();
        for &f in fs {
            let mut cx = self.cx();
            let (mut fvs, mut mask) = cx.elab_binders(&f.generics, &[])?;
            let ngen = fvs.len();
            let (pf, pm) = cx.elab_binders(&[], &f.params)?;
            if pf.is_empty() {
                return err(
                    f.name.span,
                    "a function of a `mutual` group needs a parameter to recurse on",
                );
            }
            fvs.extend(&pf);
            mask.extend(pm);
            let x = pf[0];
            let xty = from_kernel(cx.tc.local_ty(x), span)?;
            cx.tc.zonk_locals();
            let xty = cx.tc.zonk(&xty);
            let w = from_kernel(cx.tc.whnf(&xty), span)?;
            cx.tc.zonk_locals();
            let w = cx.tc.zonk(&w);
            let (h, targs) = app_spine(&w);
            let Term::Const(iname, ilevels) = &*h else {
                return err(
                    f.params[0].name.span,
                    "the first parameter must have an inductive type",
                );
            };
            let nparams = match self.env.get(iname) {
                Some(Decl::Inductive(i)) => i.nparams,
                _ => {
                    return err(
                        f.params[0].name.span,
                        "the first parameter must have an inductive type",
                    )
                }
            };
            let params: Vec<T> = targs[..nparams].to_vec();
            let ret = match &f.ret {
                Some(t) => cx.elab_type(t)?,
                None => cx.unit_type(),
            };
            cx.tc.zonk_locals();
            let ret_z = cx.tc.zonk(&ret);
            let others: Vec<u32> = pf[1..].to_vec();
            let body = cx.tc.mk_pi(&others, &ret_z);
            let lvl = from_kernel(cx.tc.check_is_type(&body), span)?;
            let lvl = cx.tc.zonk_level(&lvl);
            let motive_abs = abstract_fvars(&body, &[x]);
            let motive = cx.close(
                &fvs[..ngen],
                &lam(Mult::Omega, xty.clone(), motive_abs),
                false,
                span,
            )?;
            ms.push(Member {
                cx,
                f,
                fvs,
                mask,
                ngen,
                x,
                explicit: pf,
                ret,
                iname: iname.to_string(),
                ilevels: ilevels.clone(),
                params,
                slot: 0,
                fam_params: Vec::new(),
                lvl,
                motive,
            });
        }
        // ---- the family: one function per type, and per nested occurrence ----
        // the root is a type with nested occurrences if there is one (`Rose` for `List<Rose>`)
        let root_idx = (0..ms.len())
            .find(|&i| {
                matches!(self.env.get(&ms[i].iname), Some(Decl::Inductive(ii)) if !ii.nested.is_empty())
            })
            .unwrap_or(0);
        let root_info = match self.env.get(&ms[root_idx].iname) {
            Some(Decl::Inductive(i)) => i.clone(),
            _ => unreachable!("checked above"),
        };
        let family: Vec<String> = root_info.family.iter().map(|n| n.to_string()).collect();
        let nested = root_info.nested.clone();
        let root_params = ms[root_idx].params.clone();
        let root_closed = root_params.iter().all(first_fvar_free);
        let fam_levels = ms[root_idx].ilevels.clone();
        let mut order: Vec<Option<usize>> = vec![None; family.len() + nested.len()];
        #[allow(clippy::needless_range_loop)]
        for i in 0..ms.len() {
            let slot = if let Some(k) = family.iter().position(|f| *f == ms[i].iname) {
                ms[i].fam_params = ms[i].params.clone();
                Some(k)
            } else {
                // a nested occurrence: `J args` with `args` the nested template over the family's parameters
                let gens: Vec<T> = ms[i].fvs[..ms[i].ngen].iter().map(|&g| fvar(g)).collect();
                let fp = if root_closed {
                    root_params.clone()
                } else {
                    gens
                };
                let found = nested.iter().position(|n| {
                    *n.ind == *ms[i].iname
                        && n.args.len() == ms[i].params.len()
                        && n.args
                            .iter()
                            .zip(&ms[i].params)
                            .all(|(a, p)| instantiate_many(a, &fp) == *p)
                });
                ms[i].fam_params = fp;
                found.map(|k| family.len() + k)
            };
            let Some(slot) = slot else {
                return err(
                    ms_span(fs, i),
                    "every function of a `mutual` group must recurse on a type of one family (or a type nested in it)",
                );
            };
            if order[slot].is_some() {
                return err(
                    ms_span(fs, i),
                    "only one function per type of a mutual family is supported",
                );
            }
            ms[i].slot = slot;
            order[slot] = Some(i);
        }
        let order: Vec<usize> = match order.into_iter().collect::<Option<Vec<_>>>() {
            Some(o) => o,
            None => {
                return err(
                    span,
                    "the `mutual` group needs a function on every type of the family (and on each nested occurrence)",
                )
            }
        };
        if ms.iter().any(|m| m.lvl != ms[0].lvl) {
            return err(
                span,
                "the functions of a `mutual` group must return types in the same universe",
            );
        }
        {
            let shape = |m: &Member| -> Vec<T> {
                m.params
                    .iter()
                    .map(|p| abstract_fvars(p, &m.fvs[..m.ngen]))
                    .collect()
            };
            let first = shape(&ms[root_idx]);
            if ms
                .iter()
                .filter(|m| m.slot < family.len())
                .any(|m| shape(m) != first)
            {
                return err(
                    span,
                    "the functions of a `mutual` group must use the same type arguments for the family",
                );
            }
        }
        let siblings: Vec<(String, usize)> = ms
            .iter()
            .map(|m| (m.f.name.name.clone(), m.f.params.len()))
            .collect();
        let closed_motives: Vec<T> = order.iter().map(|&i| ms[i].motive.clone()).collect();

        // ---- phase B: the bodies, collecting the minor premises of each type ----
        let mut minors: Vec<Vec<(String, T)>> = Vec::new();
        for m in ms.iter_mut() {
            let gens: Vec<T> = m.fvs[..m.ngen].iter().map(|&g| fvar(g)).collect();
            let motives: Vec<T> = closed_motives
                .iter()
                .map(|c| head_beta(&mk_apps(c, &gens)))
                .collect();
            m.cx.rec = Some(RecCtx {
                name: m.f.name.name.clone(),
                decr: m.x,
                explicit: m.explicit.clone(),
                fields: HashMap::new(),
                refined: Vec::new(),
                in_top: false,
                deep: None,
                wf: None,
                mutual: Some(MutualCtx {
                    siblings: siblings.clone(),
                    motives,
                    view: (m.slot >= family.len()).then(|| AuxView {
                        nested_idx: m.slot - family.len(),
                        root: family[0].clone(),
                        fam_params: m.fam_params.clone(),
                        fam_levels: fam_levels.clone(),
                    }),
                }),
            });
            let Some(block) = &m.f.body else {
                return err(m.f.name.span, "a function needs a body");
            };
            let ret = m.ret.clone();
            m.cx.mutual_minors.clear();
            m.cx.scoped(|cx| {
                let v = cx.elab_block_opts(block, Some(&ret), true)?;
                cx.coerce(v, &ret, block.span)
            })?;
            let own = std::mem::take(&mut m.cx.mutual_minors);
            if own.is_empty() {
                return err(
                    m.f.name.span,
                    "the body of a `mutual` function must `match` on its first parameter",
                );
            }
            let gen_fvs: Vec<u32> = m.fvs[..m.ngen].to_vec();
            let mut closed = Vec::new();
            for (c, t) in own {
                let t = m.cx.close(&gen_fvs, &t, false, span)?;
                closed.push((c, t));
            }
            minors.push(closed);
        }

        // ---- phase C: the definitions through the shared recursor ----
        let mut out = Vec::new();
        for (i, m) in ms.iter_mut().enumerate() {
            let gens: Vec<T> = m.fvs[..m.ngen].iter().map(|&g| fvar(g)).collect();
            let motives: Vec<T> = closed_motives
                .iter()
                .map(|c| head_beta(&mk_apps(c, &gens)))
                .collect();
            let rec_name = if m.slot < family.len() {
                match self.env.get(&family[m.slot]) {
                    Some(Decl::Inductive(i)) => i.rec.clone(),
                    _ => unreachable!("family member"),
                }
            } else {
                nested[m.slot - family.len()].rec.clone()
            };
            let large = match self.env.get(&root_info.rec) {
                Some(Decl::Rec(r)) => r.lparams.len() > root_info.lparams.len(),
                _ => return err(span, "missing recursor"),
            };
            let mut rec_levels = fam_levels.clone();
            if large {
                rec_levels.insert(0, m.lvl.clone());
            } else if !m.lvl.is_zero() {
                return err(
                    span,
                    "a Prop-valued family can only be eliminated into Prop",
                );
            }
            let mut all_minors = Vec::new();
            for (k, &member) in order.iter().enumerate() {
                let (ctors, tname): (Vec<String>, String) = if k < family.len() {
                    match self.env.get(&family[k]) {
                        Some(Decl::Inductive(i)) => (
                            i.ctors.iter().map(|c| c.to_string()).collect(),
                            family[k].clone(),
                        ),
                        _ => unreachable!("family member"),
                    }
                } else {
                    let n = &nested[k - family.len()];
                    (
                        n.ctors.iter().map(|c| c.to_string()).collect(),
                        n.ind.to_string(),
                    )
                };
                let have = &minors[member];
                if have.len() != ctors.len() || have.iter().zip(&ctors).any(|((c, _), d)| c != d) {
                    return err(
                        ms_span(fs, member),
                        format!("the `match` of `{}` must have one arm for each constructor of `{tname}`", fs[member].name.name),
                    );
                }
                for (_, t) in have {
                    all_minors.push(head_beta(&mk_apps(t, &gens)));
                }
            }
            let mut args = m.fam_params.clone();
            args.extend(motives);
            args.extend(all_minors);
            args.push(fvar(m.x));
            args.extend(m.explicit[1..].iter().map(|&o| fvar(o)));
            let body = mk_apps(&cnst(rec_name, rec_levels), &args);
            let _ = i;
            let fvs = m.fvs.clone();
            let ret = m.ret.clone();
            out.push((
                m.cx.close(&fvs, &ret, true, span)?,
                m.cx.close(&fvs, &body, false, span)?,
                m.mask.clone(),
            ));
        }
        Ok(out)
    }
}

fn ms_span(fs: &[&FnDecl], i: usize) -> Span {
    fs[i].name.span
}

/// Does the term mention no free variable?
fn first_fvar_free(t: &T) -> bool {
    !has_fvar(t)
}
