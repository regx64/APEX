//! `auto`: a small proof search in the spirit of `aesop`.
//!
//! It closes a goal by trying, in order: a matching hypothesis, `rfl`, `True`,
//! `contradiction`, introducing assumptions, splitting `∧`, choosing a side of `∨`,
//! `simp`, `omega`, destructing hypotheses (`∧`, `∨`, `∃`, `False`, inductive predicates
//! are left alone), and applying implications among the hypotheses. Every choice point
//! backtracks. Like every tactic it only builds a term; the kernel checks the result.

use super::*;
use std::collections::HashSet;

const DEPTH: u32 = 6;

impl<'a> Cx<'a> {
    pub(super) fn t_auto(&mut self, st: &mut Tac, g: Goal, span: Span) -> R<Vec<Goal>> {
        let shown = self.show_goal(&g);
        let mut seen = HashSet::new();
        if self.auto_goal(st, g, DEPTH, &mut seen, span) {
            Ok(vec![])
        } else {
            err(
                span,
                format!("`auto` could not close the goal (search depth {DEPTH})\n{shown}"),
            )
        }
    }

    /// Run `f`; undo every effect if it does not succeed.
    fn attempt(&mut self, st: &mut Tac, f: impl FnOnce(&mut Self, &mut Tac) -> R<bool>) -> bool {
        let snap = self.tc.snapshot();
        let sol = st.sol.clone();
        let goals = st.goals.clone();
        match f(self, st) {
            Ok(true) => true,
            _ => {
                self.tc.restore(snap);
                st.sol = sol;
                st.goals = goals;
                false
            }
        }
    }

    fn auto_all(
        &mut self,
        st: &mut Tac,
        goals: Vec<Goal>,
        depth: u32,
        seen: &mut HashSet<u32>,
        span: Span,
    ) -> bool {
        // the destructed hypotheses are per branch: a sibling goal still has its own copy
        let base = seen.clone();
        goals.into_iter().all(|g| {
            let mut mine = base.clone();
            self.auto_goal(st, g, depth, &mut mine, span)
        })
    }

    fn auto_goal(
        &mut self,
        st: &mut Tac,
        g: Goal,
        depth: u32,
        seen: &mut HashSet<u32>,
        span: Span,
    ) -> bool {
        if depth == 0 {
            return false;
        }
        // solved by unification elsewhere
        if !matches!(&*self.tc.zonk(&mvar(g.mv)), Term::MVar(_)) {
            return true;
        }
        self.scope = g.scope.clone();
        let tgt = self.tc.zonk(&g.target);
        if self.close_by_hyp(st, &g) || self.try_rfl(st, &g) {
            return true;
        }
        let w = match self.tc.whnf(&tgt) {
            Ok(w) => w,
            Err(_) => return false,
        };
        let (h, args) = app_spine(&w);
        let head = match &*h {
            Term::Const(n, _) => n.to_string(),
            _ => String::new(),
        };
        if head == "True" {
            self.solve(st, &g, cnst("True.intro".into(), vec![]));
            return true;
        }
        // introduce assumptions
        if matches!(&*w, Term::Pi(..)) {
            let gc = g.clone();
            let mut next = None;
            let ok = self.attempt(st, |cx, st| {
                let mut gs = cx.t_intro(
                    st,
                    gc,
                    &[Ident {
                        name: "h".into(),
                        span,
                    }],
                    span,
                )?;
                next = Some(gs.remove(0));
                Ok(true)
            });
            if ok {
                if let Some(ng) = next {
                    return self.auto_goal(st, ng, depth, seen, span);
                }
            }
        }
        // destruct a hypothesis of a splitting shape
        let hyps: Vec<(String, u32, String)> = g
            .scope
            .iter()
            .filter_map(|(n, v)| match &**v {
                Term::FVar(id) if !seen.contains(id) => {
                    let ty = self.tc.zonk(&self.tc.local_ty(*id).ok()?);
                    let (hh, _) = app_spine(&ty);
                    match &*hh {
                        Term::Const(c, _) if matches!(&**c, "And" | "Or" | "Exists" | "False") => {
                            Some((n.clone(), *id, c.to_string()))
                        }
                        _ => None,
                    }
                }
                _ => None,
            })
            .collect();
        if let Some((name, id, _)) = hyps.into_iter().next() {
            seen.insert(id);
            let gc = g.clone();
            let mut parts = Vec::new();
            let x = Ident {
                name: plain_name(&name).to_string(),
                span,
            };
            let ok = self.attempt(st, |cx, st| {
                parts = cx.t_induct(st, gc, &x, &[], None, false, span)?;
                Ok(true)
            });
            if ok {
                return self.auto_all(st, parts, depth - 1, seen, span);
            }
        }
        // conjunction: both parts
        if head == "And" && args.len() == 2 {
            let g1 = self.new_goal(&g, args[0].clone(), "");
            let g2 = self.new_goal(&g, args[1].clone(), "");
            let pf = mk_apps(
                &cnst("And.intro".into(), vec![]),
                &[args[0].clone(), args[1].clone(), mvar(g1.mv), mvar(g2.mv)],
            );
            let gc = g.clone();
            return self.attempt(st, |cx, st| {
                cx.solve(st, &gc, pf);
                Ok(cx.auto_all(st, vec![g1, g2], depth - 1, seen, span))
            });
        }
        // disjunction: either side
        if head == "Or" && args.len() == 2 {
            for (k, name) in ["Or.inl", "Or.inr"].iter().enumerate() {
                let gk = self.new_goal(&g, args[k].clone(), "");
                let pf = mk_apps(
                    &cnst((*name).into(), vec![]),
                    &[args[0].clone(), args[1].clone(), mvar(gk.mv)],
                );
                let gc = g.clone();
                if self.attempt(st, |cx, st| {
                    cx.solve(st, &gc, pf);
                    Ok(cx.auto_goal(st, gk, depth - 1, seen, span))
                }) {
                    return true;
                }
            }
        }
        // contradiction, simp, omega
        let gc = g.clone();
        if self.attempt(st, |cx, st| {
            Ok(cx.t_contradiction(st, gc, span)?.is_empty())
        }) {
            return true;
        }
        let gc = g.clone();
        if self.attempt(st, |cx, st| {
            Ok(cx
                .t_simp(st, gc, &[], None, SimpOpts::default(), span)?
                .is_empty())
        }) {
            return true;
        }
        if self.env.get("omega_sound").is_some() {
            let gc = g.clone();
            if self.attempt(st, |cx, st| Ok(cx.t_omega(st, gc, span)?.is_empty())) {
                return true;
            }
        }
        // forward reasoning: `h : A -> B` and `a : A` give `B`
        let fwd: Vec<(u32, T, T)> = {
            let mut out = Vec::new();
            for (_, v) in &g.scope {
                let Term::FVar(id) = &**v else { continue };
                if seen.contains(id) {
                    continue;
                }
                let Ok(ty) = self.tc.local_ty(*id) else {
                    continue;
                };
                let ty = self.tc.zonk(&ty);
                let Ok(w) = self.tc.whnf(&ty) else { continue };
                let Term::Pi(_, dom, body) = &*w else {
                    continue;
                };
                if has_loose_bvar(body) {
                    continue;
                }
                for (_, a) in &g.scope {
                    let Term::FVar(aid) = &**a else { continue };
                    if aid == id {
                        continue;
                    }
                    let Ok(aty) = self.tc.local_ty(*aid) else {
                        continue;
                    };
                    let aty = self.tc.zonk(&aty);
                    if self.def_eq(&aty, dom) {
                        out.push((*id, app(v.clone(), a.clone()), body.clone()));
                        break;
                    }
                }
            }
            out
        };
        if let Some((id, pf, ty)) = fwd.into_iter().next() {
            seen.insert(id);
            let ng = self.add_hyp(st, &g, "fwd", ty, pf);
            if self.auto_goal(st, ng, depth - 1, seen, span) {
                return true;
            }
        }
        // apply an implication from the context
        let cands: Vec<T> = g
            .scope
            .iter()
            .filter_map(|(_, v)| match &**v {
                Term::FVar(id) => {
                    let ty = self.tc.zonk(&self.tc.local_ty(*id).ok()?);
                    let w = self.tc.whnf(&ty).ok()?;
                    matches!(&*w, Term::Pi(..)).then(|| v.clone())
                }
                _ => None,
            })
            .collect();
        for f in cands {
            let gc = g.clone();
            let mut sub = Vec::new();
            let ok = self.attempt(st, |cx, st| {
                sub = cx.apply_term(st, &gc, f, span)?;
                Ok(true)
            });
            if ok {
                let snapshot_ok = self.attempt(st, |cx, st| {
                    Ok(cx.auto_all(st, sub.clone(), depth - 1, seen, span))
                });
                if snapshot_ok {
                    return true;
                }
            }
        }
        false
    }
}
