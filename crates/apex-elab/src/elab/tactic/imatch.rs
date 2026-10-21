//! Dependent `match` on an indexed family (`Vec<T, n>`, `Even(n)`).
//!
//! The match is compiled by the tactic engine: `cases` on the scrutinee gives one goal
//! per constructor, with the indices unified by *equations* (`heq0 : m + 1 = n + 1`).
//! Each equation over `Nat` is solved by eliminating a variable (`cases` on an
//! `Eq` whose right side is that variable, so the kernel transports everything that
//! depended on it) or found contradictory (`omega`): a constructor whose indices cannot
//! match needs no arm. Each remaining arm body is elaborated as a term against its goal.

use super::*;

impl<'a> Cx<'a> {
    /// Is the type of `x` an indexed family?
    pub(in crate::elab) fn is_indexed(&mut self, x: u32) -> bool {
        let Ok(ty) = self.tc.local_ty(x) else {
            return false;
        };
        let ty = self.tc.zonk(&ty);
        let Ok(w) = self.tc.whnf(&ty) else {
            return false;
        };
        let (h, _) = app_spine(&w);
        matches!(&*h, Term::Const(n, _)
            if matches!(self.env.get(n), Some(Decl::Inductive(i)) if i.nindices > 0))
    }

    pub(in crate::elab) fn elab_indexed_match(
        &mut self,
        x: u32,
        arms: &[Arm],
        ret: &T,
        span: Span,
    ) -> R<T> {
        if !self.state_vars().is_empty() {
            return err(
                span,
                "a dependent `match` cannot assign to mutable variables of the enclosing function",
            );
        }
        let ret = self.tc.zonk(ret);
        if first_mvar(&ret).is_some() {
            return err(
                span,
                "a `match` on an indexed family needs a known result type; annotate the function or the `let`",
            );
        }
        let saved_scope = self.scope.clone();
        // the scrutinee's name in the scope (it may be a hidden temporary)
        let xname = match self
            .scope
            .iter()
            .rfind(|(_, v)| matches!(&**v, Term::FVar(i) if *i == x))
        {
            Some((n, _)) => plain_name(n).to_string(),
            None => {
                self.scope.push(("__scrut".into(), fvar(x)));
                "__scrut".to_string()
            }
        };
        // the scrutinee's inductive type
        let xty = from_kernel(self.tc.local_ty(x), span)?;
        let xty = self.tc.zonk(&xty);
        let w = from_kernel(self.tc.whnf(&xty), span)?;
        let (h, _) = app_spine(&w);
        let Term::Const(iname, _) = &*h else {
            return err(span, "cannot match on this value");
        };
        let iname = iname.to_string();
        let ctors: Vec<String> = match self.env.get(&iname) {
            Some(Decl::Inductive(i)) => i.ctors.iter().map(|c| c.to_string()).collect(),
            _ => return err(span, "cannot match on this value"),
        };
        // arms by constructor; a `_` arm covers the rest
        struct ArmInfo<'e> {
            names: Vec<String>,
            body: &'e Expr,
        }
        let mut by_ctor: HashMap<String, ArmInfo> = HashMap::new();
        let mut default: Option<&Expr> = None;
        for a in arms {
            match self.elab_pattern(&a.pat)? {
                Pat::Ctor(full, subs) => {
                    let mut names = Vec::new();
                    for (k, p) in subs.iter().enumerate() {
                        names.push(match p {
                            Pat::Var(n) => n.clone(),
                            Pat::Wild => format!("_w{k}"),
                            Pat::Ctor(..) => {
                                return err(
                                    a.pat.span,
                                    "nested patterns on an indexed family: match the field in a nested `match`",
                                )
                            }
                        });
                    }
                    if !ctors.contains(&full) {
                        return err(
                            a.pat.span,
                            format!("`{full}` is not a constructor of `{iname}`"),
                        );
                    }
                    by_ctor.insert(
                        short(&full).to_string(),
                        ArmInfo {
                            names,
                            body: &a.body,
                        },
                    );
                }
                Pat::Wild => default = Some(&a.body),
                Pat::Var(_) => {
                    return err(
                        a.pat.span,
                        "use `_` for a catch-all arm on an indexed family",
                    )
                }
            }
        }
        // binder names for the constructor fields: implicit locals are hidden
        let mut case_names: HashMap<String, Vec<String>> = HashMap::new();
        for c in &ctors {
            let (nfields, nparams) = match self.env.get(c) {
                Some(Decl::Ctor(ci)) => (ci.nfields, ci.nparams),
                _ => return err(span, "internal error: missing constructor"),
            };
            let nlocal = self
                .masks
                .get(c)
                .map_or(0, |m| m.len().saturating_sub(nparams));
            let mut names: Vec<String> = (0..nlocal).map(|i| format!("__l{i}")).collect();
            match by_ctor.get(short(c)) {
                Some(a) => {
                    if a.names.len() + nlocal != nfields {
                        return err(
                            a.body.span,
                            format!(
                                "constructor `{}` takes {} fields, the pattern has {}",
                                short(c),
                                nfields - nlocal,
                                a.names.len()
                            ),
                        );
                    }
                    names.extend(a.names.iter().cloned());
                }
                None => names.extend((nlocal..nfields).map(|i| format!("__f{i}"))),
            }
            names.extend((0..8).map(|i| format!("__ih{i}")));
            case_names.insert(short(c).to_string(), names);
        }
        // recursion on the scrutinee: the other parameters are generalized, as in `compile_match`
        let is_decr = self.rec.as_ref().is_some_and(|rc| rc.decr == x);
        let mut others: Vec<Ident> = Vec::new();
        if is_decr {
            if let Some(rc) = &self.rec {
                for &p in &rc.explicit {
                    if p == x {
                        continue;
                    }
                    if let Some((n, _)) = self
                        .scope
                        .iter()
                        .rfind(|(_, v)| matches!(&**v, Term::FVar(i) if *i == p))
                    {
                        others.push(Ident {
                            name: plain_name(n).to_string(),
                            span,
                        });
                    }
                }
            }
        }

        let mv = self.tc.new_mvar(ret.clone());
        let g0 = Goal {
            mv: mvar_id(&mv),
            scope: self.scope.clone(),
            target: ret,
            tag: String::new(),
        };
        let mut st = Tac::default();
        self.case_names = Some(case_names);
        let xid = Ident { name: xname, span };
        let goals = self.t_induct(&mut st, g0, &xid, &others, None, is_decr, span);
        self.case_names = None;
        let goals = goals?;

        for bg in goals {
            let ctor = bg.tag.clone();
            let body = by_ctor.get(&ctor).map(|a| a.body).or(default);
            let Some(body) = body else {
                // no arm: fine if the indices make the constructor impossible
                match self.solve_index_equations(&mut st, bg, span)? {
                    None => continue,
                    Some(_) => {
                        self.scope = saved_scope;
                        return err(span, format!("non-exhaustive patterns: missing `{ctor}`"));
                    }
                }
            };
            let Some(bg) = self.solve_index_equations(&mut st, bg, span)? else {
                continue; // impossible, whatever the arm says
            };
            if is_decr {
                self.register_branch_ihs(&bg, &iname);
            }
            self.scope = bg.scope.clone();
            let t = self.elab_check(body, &bg.target)?;
            self.solve_goals(false)?;
            let t = self.tc.zonk(&t);
            self.solve(&mut st, &bg, t);
        }
        self.scope = saved_scope;
        self.tc.zonk_locals();
        Ok(self.build(&st, &mv))
    }

    /// The induction hypotheses of a branch, by their names `__ih0, ..`, belong to the
    /// recursive fields in order.
    fn register_branch_ihs(&mut self, bg: &Goal, iname: &str) {
        let lookup = |name: &str| {
            bg.scope
                .iter()
                .rfind(|(n, _)| n == name)
                .map(|(_, v)| v.clone())
        };
        // recursive fields: the branch variables whose type mentions the family
        let mut rec_fields: Vec<T> = Vec::new();
        for (_, v) in &bg.scope {
            if let Term::FVar(id) = &**v {
                if let Ok(ty) = self.tc.local_ty(*id) {
                    let name = &bg
                        .scope
                        .iter()
                        .find(|(_, w)| w == v)
                        .map(|(n, _)| n.clone());
                    let hidden_ih = name.as_ref().is_some_and(|n| n.starts_with("__ih"));
                    if !hidden_ih
                        && contains_const(&self.tc.zonk(&ty), iname)
                        && name.is_some()
                        && !bg.tag.is_empty()
                        && self.is_branch_var(bg, *id)
                    {
                        rec_fields.push(v.clone());
                    }
                }
            }
        }
        for (k, f) in rec_fields.iter().enumerate() {
            if let (Some(ih), Term::FVar(fid)) = (lookup(&format!("__ih{k}")), &**f) {
                if let Some(rc) = &mut self.rec {
                    rc.fields.insert(*fid, ih);
                }
            }
        }
    }

    /// A variable introduced by the case split (not a parameter of the function).
    fn is_branch_var(&self, bg: &Goal, id: u32) -> bool {
        let outer: Vec<u32> = self
            .rec
            .as_ref()
            .map(|rc| rc.explicit.clone())
            .unwrap_or_default();
        !outer.contains(&id)
            && bg
                .scope
                .iter()
                .any(|(n, v)| matches!(&**v, Term::FVar(i) if *i == id) && !n.starts_with("__ih"))
    }

    /// Solve the index equations `heq_i` of a branch. `None`: they are contradictory and
    /// the branch is closed; otherwise the goal with the indices unified.
    fn solve_index_equations(&mut self, st: &mut Tac, g: Goal, span: Span) -> R<Option<Goal>> {
        let mut g = g;
        for _ in 0..32 {
            // the next equation
            let mut found = None;
            for (i, (n, v)) in g.scope.iter().enumerate() {
                if !n.starts_with("heq") {
                    continue;
                }
                let Term::FVar(id) = &**v else { continue };
                let Ok(ty) = self.tc.local_ty(*id) else {
                    continue;
                };
                found = Some((i, n.clone(), *id, self.tc.zonk(&ty)));
                break;
            }
            let Some((pos, name, _id, ty)) = found else {
                return Ok(Some(g));
            };
            let Some((_, alpha, a, b)) = self.eq_parts(&ty) else {
                g.scope.remove(pos);
                continue;
            };
            if !matches!(&*alpha, Term::Const(n, _) if &**n == "Nat") {
                return err(
                    span,
                    "the indices of this family are not natural numbers: dependent `match` supports `Nat` indices",
                );
            }
            let (a, b) = (self.devirt(&a), self.devirt(&b));
            let (la, lb) = (self.nat_lin(&a), self.nat_lin(&b));
            let (Some((va, ca)), Some((vb, cb))) = (la, lb) else {
                return err(
                    span,
                    format!(
                        "cannot unify the indices `{} = {}`: only variables plus literals are supported",
                        self.pp(&a),
                        self.pp(&b)
                    ),
                );
            };
            // decide what the equation says: drop it, contradiction, or eliminate a variable
            enum Step {
                Drop,
                Contradiction,
                Eliminate(u32, Option<u32>, u64), // v := (other var)? + constant
            }
            let step = match (va, vb) {
                (None, None) => {
                    if ca == cb {
                        Step::Drop
                    } else {
                        Step::Contradiction
                    }
                }
                (Some(v), None) => {
                    if cb >= ca {
                        Step::Eliminate(v, None, cb - ca)
                    } else {
                        Step::Contradiction
                    }
                }
                (None, Some(v)) => {
                    if ca >= cb {
                        Step::Eliminate(v, None, ca - cb)
                    } else {
                        Step::Contradiction
                    }
                }
                (Some(v1), Some(v2)) if v1 == v2 => {
                    if ca == cb {
                        Step::Drop
                    } else {
                        Step::Contradiction
                    }
                }
                (Some(v1), Some(v2)) => {
                    // eliminate the newer variable (larger id): it is the constructor's own
                    let (elim, keep, ce, ck) = if v1 > v2 {
                        (v1, v2, ca, cb)
                    } else {
                        (v2, v1, cb, ca)
                    };
                    if ck >= ce {
                        Step::Eliminate(elim, Some(keep), ck - ce)
                    } else {
                        Step::Eliminate(keep, Some(elim), ce - ck)
                    }
                }
            };
            match step {
                Step::Drop => {
                    g.scope.remove(pos);
                }
                Step::Contradiction => {
                    // False from the equation, then omega finds it
                    let tgt = self.tc.zonk(&g.target);
                    let lvl = self.sort_level_of(&tgt, span)?;
                    let fg = self.new_goal(&g, cnst("False".into(), vec![]), "");
                    let pf = mk_apps(&cnst("False.elim".into(), vec![lvl]), &[tgt, mvar(fg.mv)]);
                    self.solve(st, &g, pf);
                    self.t_omega(st, fg, span)?;
                    return Ok(None);
                }
                Step::Eliminate(v, other, c) => {
                    let mut expr = lit(c as u128);
                    if let Some(o) = other {
                        expr = mk_apps(&cnst("Nat.add".into(), vec![]), &[fvar(o), lit(c as u128)]);
                    }
                    // hm : expr = v, by omega from the equation; then `cases hm` substitutes `v`
                    let hm_ty = mk_apps(
                        &cnst("Eq".into(), vec![Level::of_nat(1)]),
                        &[cnst("Nat".into(), vec![]), expr, fvar(v)],
                    );
                    let pg = self.new_goal(&g, hm_ty.clone(), "");
                    let pmv = pg.mv;
                    self.t_omega(st, pg, span)?;
                    let _ = name;
                    let ng = self.add_hyp(st, &g, "hm", hm_ty, mvar(pmv));
                    let x = Ident {
                        name: "hm".into(),
                        span,
                    };
                    let mut gs = self.t_induct(st, ng, &x, &[], None, false, span)?;
                    if gs.len() != 1 {
                        return err(span, "internal error: index elimination split the goal");
                    }
                    let mut next = gs.remove(0);
                    next.tag = g.tag.clone();
                    g = next;
                }
            }
        }
        Ok(Some(g))
    }
}
