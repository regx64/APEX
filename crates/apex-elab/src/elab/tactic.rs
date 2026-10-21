//! Tactic proofs (`by { ... }`).
//!
//! A tactic proof is a *program that builds a proof term*. The state is a list of
//! goals, each a metavariable with its own local context. A tactic solves the first
//! goal with a term that may mention fresh goals; `intro`-like tactics solve it with
//! a λ whose body is a fresh goal. At the end the solutions are substituted
//! together into one term, which the kernel checks like any other definition, so
//! tactics are untrusted: a buggy tactic can only produce an error, not a false theorem.

use super::*;

mod auto;
mod extra;
mod imatch;
mod noconf;
mod omega;

/// Options of `simp`.
#[derive(Default, Clone, Copy)]
struct SimpOpts {
    /// `simp only`: no `#[simp]` library.
    only: bool,
    /// `simp_all`: equations among the hypotheses are rules too.
    all_hyps: bool,
}

/// One open goal.
#[derive(Clone)]
struct Goal {
    /// The metavariable standing for the proof.
    mv: u32,
    /// Hypotheses (and parameters) in scope, oldest first.
    scope: Vec<(String, T)>,
    target: T,
    /// Which case this goal came from (`zero`, `succ`, ...), for messages.
    tag: String,
}

#[derive(Clone)]
enum Sol {
    Term(T),
    /// `fun fvs => body`, where `body` is another goal.
    Lam(Vec<u32>, u32),
}

#[derive(Default)]
struct Tac {
    goals: Vec<Goal>,
    sol: HashMap<u32, Sol>,
}

/// A lemma `∀ args, lhs = rhs`, opened with a metavariable per argument.
struct OpenRule {
    /// The proof of `lhs = rhs`, applied to the argument metavariables.
    proof: T,
    args: Vec<T>,
    level: Level,
    alpha: T,
    lhs: T,
    rhs: T,
}

fn mvar_id(t: &T) -> u32 {
    match &**t {
        Term::MVar(i) => *i,
        _ => unreachable!("not a metavariable"),
    }
}

fn collect_subterms(t: &T, out: &mut Vec<T>) {
    if !has_loose_bvar(t) {
        out.push(t.clone());
    }
    match &**t {
        Term::App(f, a) => {
            collect_subterms(f, out);
            collect_subterms(a, out);
        }
        Term::Lam(_, ty, b) | Term::Pi(_, ty, b) => {
            collect_subterms(ty, out);
            collect_subterms(b, out);
        }
        Term::Let(_, ty, v, b) => {
            collect_subterms(ty, out);
            collect_subterms(v, out);
            collect_subterms(b, out);
        }
        _ => {}
    }
}

/// Replace every occurrence of the closed term `s` in `t` by the bound variable
/// that the enclosing motive binds.
fn replace_term(t: &T, s: &T, depth: u32) -> T {
    if t == s {
        return bvar(depth);
    }
    match &**t {
        Term::App(f, a) => app(replace_term(f, s, depth), replace_term(a, s, depth)),
        Term::Lam(m, ty, b) => lam(
            *m,
            replace_term(ty, s, depth),
            replace_term(b, s, depth + 1),
        ),
        Term::Pi(m, ty, b) => pi(
            *m,
            replace_term(ty, s, depth),
            replace_term(b, s, depth + 1),
        ),
        Term::Let(m, ty, v, b) => let_(
            *m,
            replace_term(ty, s, depth),
            replace_term(v, s, depth),
            replace_term(b, s, depth + 1),
        ),
        _ => t.clone(),
    }
}

/// Replace the constant `name` by `val` and reduce the beta-redexes this creates.
fn unfold_const(t: &T, name: &str, val: &dyn Fn(&[Level]) -> T) -> T {
    match &**t {
        Term::App(..) => {
            let (f, args) = app_spine(t);
            let args: Vec<T> = args.iter().map(|a| unfold_const(a, name, val)).collect();
            let f = unfold_const(&f, name, val);
            head_beta(&mk_apps(&f, &args))
        }
        Term::Const(n, ls) if &**n == name => val(ls),
        Term::Lam(m, ty, b) => lam(*m, unfold_const(ty, name, val), unfold_const(b, name, val)),
        Term::Pi(m, ty, b) => pi(*m, unfold_const(ty, name, val), unfold_const(b, name, val)),
        Term::Let(m, ty, v, b) => let_(
            *m,
            unfold_const(ty, name, val),
            unfold_const(v, name, val),
            unfold_const(b, name, val),
        ),
        _ => t.clone(),
    }
}

fn short(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}

impl<'a> Cx<'a> {
    // ---- driver ----

    /// Prove `target` with `tactics`, in the current scope. The result is a kernel
    /// term (unchecked: the caller's definition is checked by the kernel).
    pub(super) fn prove(&mut self, target: &T, tactics: &[Tactic], span: Span) -> R<T> {
        let saved = self.scope.clone();
        let target = {
            let z = self.tc.zonk(target);
            self.devirt(&z)
        };
        // hypotheses are shown and matched in their devirtualized form too
        for (_, v) in &saved {
            if let Term::FVar(id) = &**v {
                if let Ok(ty) = self.tc.local_ty(*id) {
                    let z = self.tc.zonk(&ty);
                    let d = self.devirt(&z);
                    self.tc.set_local_ty(*id, d);
                }
            }
        }
        let mv = self.tc.new_mvar(target.clone());
        let mut st = Tac {
            goals: vec![Goal {
                mv: mvar_id(&mv),
                scope: saved.clone(),
                target,
                tag: String::new(),
            }],
            sol: HashMap::new(),
        };
        let r = self.run_seq(&mut st, tactics);
        self.scope = saved;
        r?;
        if let Some(g) = st.goals.first() {
            let all: Vec<String> = st.goals.iter().map(|g| self.show_goal(g)).collect();
            let _ = g;
            return err(span, format!("unsolved goals\n{}", all.join("\n\n")));
        }
        self.tc.zonk_locals();
        Ok(self.build(&st, &mv))
    }

    fn run_seq(&mut self, st: &mut Tac, tactics: &[Tactic]) -> R<()> {
        for t in tactics {
            self.run_one(st, t)?;
        }
        Ok(())
    }

    fn run_one(&mut self, st: &mut Tac, t: &Tactic) -> R<()> {
        if st.goals.is_empty() {
            // these are happy to have nothing to do
            if matches!(
                t.kind,
                TacticKind::Try(_)
                    | TacticKind::Skip
                    | TacticKind::Repeat(_)
                    | TacticKind::AllGoals(_)
                    | TacticKind::Done
            ) {
                return Ok(());
            }
            return err(t.span, "no goals left, but there is another tactic");
        }
        let g = st.goals.remove(0);
        if !matches!(&*self.tc.zonk(&mvar(g.mv)), Term::MVar(_)) {
            // solved as a side effect of unification
            return self.run_one(st, t);
        }
        self.scope = g.scope.clone();
        let shown = self.show_goal(&g);
        match self.step(st, g, t) {
            Ok(new_goals) => {
                let mut rest = std::mem::take(&mut st.goals);
                st.goals = new_goals;
                st.goals.append(&mut rest);
                Ok(())
            }
            Err(mut e) => {
                if !e.msg.contains("\n⊢") && !e.msg.contains("unsolved goals") {
                    e.msg = format!("{}\n{}", e.msg, shown);
                }
                Err(e)
            }
        }
    }

    /// Run `body` on the single goal `g`; it must close it.
    fn focus(&mut self, st: &mut Tac, g: Goal, body: &[Tactic], span: Span) -> R<()> {
        let rest = std::mem::replace(&mut st.goals, vec![g]);
        let r = self.run_seq(st, body);
        let left = std::mem::replace(&mut st.goals, rest);
        r?;
        if !left.is_empty() {
            let all: Vec<String> = left.iter().map(|g| self.show_goal(g)).collect();
            return err(span, format!("unsolved goals\n{}", all.join("\n\n")));
        }
        Ok(())
    }

    fn show_goal(&self, g: &Goal) -> String {
        let mut s = String::new();
        if !g.tag.is_empty() {
            s.push_str(&format!("case {}\n", g.tag));
        }
        for (n, t) in &g.scope {
            if n.starts_with('\u{1}') || n.starts_with('\'') {
                continue;
            }
            if let Term::FVar(id) = &**t {
                if let Ok(ty) = self.tc.local_ty(*id) {
                    s.push_str(&format!("{n} : {}\n", self.pp_prop(&ty)));
                }
            }
        }
        s.push_str(&format!("⊢ {}", self.pp_prop(&g.target)));
        s
    }

    /// Print a proposition the way it is written: `a = b`, `And<P, Q>`.
    fn pp_prop(&self, t: &T) -> String {
        let t = self.tc.zonk(t);
        let (h, args) = app_spine(&t);
        if let Term::Const(n, _) = &*h {
            match (&**n, args.len()) {
                ("Eq", 3) => {
                    return format!("{} = {}", self.pp(&args[1]), self.pp(&args[2]));
                }
                ("And" | "Or", 2) => {
                    return format!(
                        "{}<{}, {}>",
                        n,
                        self.pp_prop(&args[0]),
                        self.pp_prop(&args[1])
                    );
                }
                _ => {}
            }
        }
        self.pp(&t)
    }

    fn new_goal(&mut self, from: &Goal, target: T, tag: &str) -> Goal {
        let mv = self.tc.new_mvar(target.clone());
        Goal {
            mv: mvar_id(&mv),
            scope: from.scope.clone(),
            target,
            tag: if tag.is_empty() {
                from.tag.clone()
            } else {
                tag.to_string()
            },
        }
    }

    fn build(&self, st: &Tac, t: &T) -> T {
        let z = self.tc.zonk(t);
        self.subst_sols(st, &z)
    }

    fn subst_sols(&self, st: &Tac, t: &T) -> T {
        match &**t {
            Term::MVar(id) => match st.sol.get(id) {
                Some(Sol::Term(s)) => self.build(st, s),
                Some(Sol::Lam(fvs, body)) => {
                    let b = self.build(st, &mvar(*body));
                    self.tc.mk_lam(fvs, &b)
                }
                None => t.clone(),
            },
            Term::App(f, a) => app(self.subst_sols(st, f), self.subst_sols(st, a)),
            Term::Lam(m, ty, b) => lam(*m, self.subst_sols(st, ty), self.subst_sols(st, b)),
            Term::Pi(m, ty, b) => pi(*m, self.subst_sols(st, ty), self.subst_sols(st, b)),
            Term::Let(m, ty, v, b) => let_(
                *m,
                self.subst_sols(st, ty),
                self.subst_sols(st, v),
                self.subst_sols(st, b),
            ),
            _ => t.clone(),
        }
    }

    fn solve(&self, st: &mut Tac, g: &Goal, t: T) {
        st.sol.insert(g.mv, Sol::Term(t));
    }

    // ---- helpers over the kernel ----

    /// `Eq.{l} α a b` -> (l, α, a, b), looking through definitions.
    fn eq_parts(&mut self, t: &T) -> Option<(Level, T, T, T)> {
        let t = self.tc.zonk(t);
        let w = self.tc.whnf(&t).ok()?;
        let (h, args) = app_spine(&w);
        match &*h {
            Term::Const(n, ls) if &**n == "Eq" && args.len() == 3 && ls.len() == 1 => Some((
                self.tc.zonk_level(&ls[0]),
                args[0].clone(),
                args[1].clone(),
                args[2].clone(),
            )),
            _ => None,
        }
    }

    fn def_eq(&mut self, a: &T, b: &T) -> bool {
        let snap = self.tc.snapshot();
        match self.tc.is_def_eq(a, b) {
            Ok(true) => true,
            _ => {
                self.tc.restore(snap);
                false
            }
        }
    }

    fn elab_in_goal(&mut self, e: &Expr, expected: Option<&T>) -> R<T> {
        let t = match expected {
            Some(ex) => self.elab_check(e, ex)?,
            None => self.elab(e, None)?,
        };
        self.solve_goals(false)?;
        let t = self.tc.zonk(&t);
        Ok(self.devirt(&t))
    }

    /// Close an equation whose sides are definitionally equal.
    fn try_rfl(&mut self, st: &mut Tac, g: &Goal) -> bool {
        if let Some((l, alpha, a, b)) = self.eq_parts(&g.target) {
            if self.def_eq(&a, &b) {
                let pf = mk_apps(&cnst("Eq.refl".into(), vec![l]), &[alpha, a]);
                self.solve(st, g, pf);
                return true;
            }
        }
        false
    }

    // ---- the tactics ----

    fn step(&mut self, st: &mut Tac, g: Goal, t: &Tactic) -> R<Vec<Goal>> {
        let span = t.span;
        match &t.kind {
            TacticKind::Block(body) => {
                self.focus(st, g, body, span)?;
                Ok(vec![])
            }
            TacticKind::Intro(names) => self.t_intro(st, g, names, span),
            TacticKind::Exact(e) => {
                let pf = self.elab_in_goal(e, Some(&g.target.clone()))?;
                if first_mvar(&pf).is_some() {
                    return err(e.span, "cannot infer an argument of this term");
                }
                self.solve(st, &g, pf);
                Ok(vec![])
            }
            TacticKind::Apply(e) => {
                let f = self.elab_in_goal(e, None)?;
                self.apply_term(st, &g, f, span)
            }
            TacticKind::Rfl => {
                let Some((l, alpha, a, b)) = self.eq_parts(&g.target) else {
                    return err(span, "`rfl` needs a goal of the form `a = b`");
                };
                if !self.def_eq(&a, &b) {
                    return err(
                        span,
                        format!(
                            "`rfl` failed: `{}` and `{}` are not definitionally equal",
                            self.pp(&a),
                            self.pp(&b)
                        ),
                    );
                }
                let pf = mk_apps(&cnst("Eq.refl".into(), vec![l]), &[alpha, a]);
                self.solve(st, &g, pf);
                Ok(vec![])
            }
            TacticKind::Assumption => {
                if self.close_by_hyp(st, &g) {
                    Ok(vec![])
                } else {
                    err(span, "`assumption` failed: no hypothesis matches the goal")
                }
            }
            TacticKind::Constructor => self.t_constructor(st, g, span),
            TacticKind::Left | TacticKind::Right => {
                let name = if matches!(t.kind, TacticKind::Left) {
                    "Or.inl"
                } else {
                    "Or.inr"
                };
                let (c, _) = self.const_term(name);
                self.apply_term(st, &g, c, span)
            }
            TacticKind::Exfalso => {
                let tgt = self.tc.zonk(&g.target);
                let lvl = self.sort_level_of(&tgt, span)?;
                let ng = self.new_goal(&g, cnst("False".into(), vec![]), "");
                let pf = mk_apps(&cnst("False.elim".into(), vec![lvl]), &[tgt, mvar(ng.mv)]);
                self.solve(st, &g, pf);
                Ok(vec![ng])
            }
            TacticKind::Contradiction => self.t_contradiction(st, g, span),
            TacticKind::Injection(h, names) => self.t_injection(st, g, h, names, span),
            TacticKind::Subst(n) => self.t_subst(st, g, n, span),
            TacticKind::Rcases(e, pat) => self.t_rcases(st, g, e, pat, span),
            TacticKind::Rintro(pats) => self.t_rintro(st, g, pats, span),
            TacticKind::ByCases(n, p) => self.t_by_cases(st, g, n.as_ref(), p, span),
            TacticKind::ByContra(n) => self.t_by_contra(st, g, n.as_ref(), span),
            TacticKind::Specialize(e) => self.t_specialize(st, g, e, span),
            TacticKind::Refine(e) => self.t_refine(st, g, e, span),
            TacticKind::Funext(ns) => self.t_funext(st, g, ns, span),
            TacticKind::Congr => self.t_congr(st, g, span),
            TacticKind::Calc(steps) => self.t_calc(st, g, steps, span),
            TacticKind::Trivial => self.t_trivial(st, g, span),
            TacticKind::Symm => {
                let Some((l, alpha, a, b)) = self.eq_parts(&g.target) else {
                    return err(span, "`symm` needs a goal of the form `a = b`");
                };
                let ng = self.new_goal(
                    &g,
                    mk_apps(
                        &cnst("Eq".into(), vec![l.clone()]),
                        &[alpha.clone(), b.clone(), a.clone()],
                    ),
                    "",
                );
                let pf = mk_apps(
                    &cnst("Eq.symm".into(), vec![l]),
                    &[alpha, b, a, mvar(ng.mv)],
                );
                self.solve(st, &g, pf);
                Ok(vec![ng])
            }
            TacticKind::Decide => {
                let tgt = self.tc.zonk(&g.target);
                if has_fvar(&tgt) {
                    return err(
                        span,
                        "`decide` only proves closed propositions (this goal mentions variables)",
                    );
                }
                let pf = self.decide(&tgt, span)?;
                self.solve(st, &g, pf);
                Ok(vec![])
            }
            TacticKind::Omega => self.t_omega(st, g, span),
            TacticKind::Auto => self.t_auto(st, g, span),
            TacticKind::Skip => Ok(vec![g]),
            TacticKind::Done => err(span, "`done` failed: there are goals left"),
            TacticKind::Fail(m) => err(span, m.clone()),
            TacticKind::Seq(ts) => {
                let rest = std::mem::take(&mut st.goals);
                st.goals = vec![g];
                let r = self.run_seq(st, ts);
                let produced = std::mem::replace(&mut st.goals, rest);
                r?;
                Ok(produced)
            }
            TacticKind::Try(t) => {
                let snap = self.tc.snapshot();
                let sol = st.sol.clone();
                match self.step(st, g.clone(), t) {
                    Ok(gs) => Ok(gs),
                    Err(_) => {
                        self.tc.restore(snap);
                        st.sol = sol;
                        Ok(vec![g])
                    }
                }
            }
            TacticKind::First(alts) => {
                let mut last = None;
                for t in alts {
                    let snap = self.tc.snapshot();
                    let sol = st.sol.clone();
                    match self.step(st, g.clone(), t) {
                        Ok(gs) => return Ok(gs),
                        Err(e) => {
                            self.tc.restore(snap);
                            st.sol = sol;
                            last = Some(e);
                        }
                    }
                }
                Err(last.unwrap_or_else(|| ElabError::new(span, "`first` has no alternatives")))
            }
            TacticKind::Repeat(t) => self.repeat_on(st, g, t, 64),
            TacticKind::Then(a, b) => {
                let first = self.step(st, g, a)?;
                let mut out = Vec::new();
                for ng in first {
                    out.extend(self.run_on(st, ng, b)?);
                }
                Ok(out)
            }
            TacticKind::AllGoals(t) => {
                let mut all = vec![g];
                all.extend(std::mem::take(&mut st.goals));
                let mut out = Vec::new();
                for ng in all {
                    out.extend(self.run_on(st, ng, t)?);
                }
                Ok(out)
            }
            TacticKind::AnyGoals(t) => {
                let mut all = vec![g];
                all.extend(std::mem::take(&mut st.goals));
                let (mut out, mut worked) = (Vec::new(), false);
                for ng in all {
                    let snap = self.tc.snapshot();
                    let sol = st.sol.clone();
                    match self.run_on(st, ng.clone(), t) {
                        Ok(gs) => {
                            worked = true;
                            out.extend(gs);
                        }
                        Err(_) => {
                            self.tc.restore(snap);
                            st.sol = sol;
                            out.push(ng);
                        }
                    }
                }
                if worked {
                    Ok(out)
                } else {
                    err(span, "`any_goals`: the tactic failed on every goal")
                }
            }
            TacticKind::Show(e) => {
                let ty = self.elab_type(e)?;
                self.solve_goals(false)?;
                if !self.def_eq(&ty, &g.target) {
                    return err(
                        span,
                        format!(
                            "`show` failed: `{}` is not definitionally equal to the goal `{}`",
                            self.pp(&ty),
                            self.pp(&g.target)
                        ),
                    );
                }
                let ty = self.tc.zonk(&ty);
                let ty = self.devirt(&ty);
                let ng = self.new_goal(&g, ty, "");
                self.solve(st, &g, mvar(ng.mv));
                Ok(vec![ng])
            }
            TacticKind::Have { name, ty, proof } => {
                let hty = self.elab_type(ty)?;
                self.solve_goals(false)?;
                let hty = self.tc.zonk(&hty);
                let hty = self.devirt(&hty);
                let pf = match proof {
                    HaveProof::Term(e) => self.elab_in_goal(e, Some(&hty))?,
                    HaveProof::Tactic(ts) => {
                        let saved = self.scope.clone();
                        let r = self.prove(&hty, ts, span);
                        self.scope = saved;
                        r?
                    }
                };
                let fv = self.tc.fresh(&name.name, hty.clone(), Mult::Omega);
                let mut ng = self.new_goal(&g, g.target.clone(), "");
                ng.scope.push((name.name.clone(), fvar(fv)));
                let lam_mv = self.tc.new_mvar(pi(Mult::Omega, hty, g.target.clone()));
                st.sol.insert(mvar_id(&lam_mv), Sol::Lam(vec![fv], ng.mv));
                self.solve(st, &g, app(lam_mv, pf));
                Ok(vec![ng])
            }
            TacticKind::Rw(rules, at) => self.t_rw(st, g, rules, at.as_ref(), span),
            TacticKind::Simp(lemmas, at) => {
                self.t_simp(st, g, lemmas, at.as_ref(), SimpOpts::default(), span)
            }
            TacticKind::SimpOnly(lemmas, at) => {
                let opts = SimpOpts {
                    only: true,
                    all_hyps: false,
                };
                self.t_simp(st, g, lemmas, at.as_ref(), opts, span)
            }
            TacticKind::SimpAll(lemmas) => {
                let opts = SimpOpts {
                    only: false,
                    all_hyps: true,
                };
                self.t_simp(st, g, lemmas, None, opts, span)
            }
            TacticKind::SimpArith(lemmas) => {
                let rest = match self.t_simp(st, g.clone(), lemmas, None, SimpOpts::default(), span)
                {
                    Ok(gs) => gs,
                    // nothing to simplify: omega may still do it
                    Err(e) if e.msg.contains("made no progress") => vec![g],
                    Err(e) => return Err(e),
                };
                for ng in rest {
                    self.t_omega(st, ng, span)?;
                }
                Ok(vec![])
            }
            TacticKind::Unfold(names) => {
                let mut tgt = self.tc.zonk(&g.target);
                for n in names {
                    tgt = self.unfold_in(&tgt, n)?;
                }
                let ng = self.new_goal(&g, tgt, "");
                self.solve(st, &g, mvar(ng.mv));
                if self.try_rfl(st, &ng) {
                    return Ok(vec![]);
                }
                Ok(vec![ng])
            }
            TacticKind::Induction(x, gen, arms) => {
                self.t_induct(st, g, x, gen, arms.as_deref(), true, span)
            }
            TacticKind::Revert(names) => {
                let (ng, _) = self.revert_vars(st, &g, names, span)?;
                Ok(vec![ng])
            }
            TacticKind::Exists(e) => self.t_exists(st, g, e, span),
            TacticKind::Cases(e, arms) => {
                if let ExprKind::Var(n) = &e.kind {
                    let x = Ident {
                        name: n.clone(),
                        span: e.span,
                    };
                    return self.t_induct(st, g, &x, &[], arms.as_deref(), false, span);
                }
                // a proof term: bind it to a hypothesis first
                let tm = self.elab_in_goal(e, None)?;
                let ty = from_kernel(self.tc.infer(&tm), e.span)?;
                let ty = self.tc.zonk(&ty);
                let fv = self.tc.fresh("_c", ty.clone(), Mult::Omega);
                let mut ng = self.new_goal(&g, g.target.clone(), "");
                ng.scope.push(("_c".into(), fvar(fv)));
                let lam_mv = self.tc.new_mvar(pi(Mult::Omega, ty, g.target.clone()));
                st.sol.insert(mvar_id(&lam_mv), Sol::Lam(vec![fv], ng.mv));
                self.solve(st, &g, app(lam_mv, tm));
                let x = Ident {
                    name: "_c".into(),
                    span: e.span,
                };
                self.t_induct(st, ng, &x, &[], arms.as_deref(), false, span)
            }
        }
    }

    /// Run one tactic on one goal (goal list isolation: the other goals are not touched).
    fn run_on(&mut self, st: &mut Tac, g: Goal, t: &Tactic) -> R<Vec<Goal>> {
        self.scope = g.scope.clone();
        if !matches!(&*self.tc.zonk(&mvar(g.mv)), Term::MVar(_)) {
            return Ok(vec![]); // solved by unification
        }
        self.step(st, g, t)
    }

    /// `repeat t`: apply `t` to the goal and to the goals it produces, until it fails.
    fn repeat_on(&mut self, st: &mut Tac, g: Goal, t: &Tactic, fuel: u32) -> R<Vec<Goal>> {
        if fuel == 0 {
            return Ok(vec![g]);
        }
        let snap = self.tc.snapshot();
        let sol = st.sol.clone();
        match self.run_on(st, g.clone(), t) {
            Ok(gs) => {
                // no progress: the same single goal back
                if gs.len() == 1 && gs[0].mv == g.mv {
                    return Ok(gs);
                }
                let mut out = Vec::new();
                for ng in gs {
                    out.extend(self.repeat_on(st, ng, t, fuel - 1)?);
                }
                Ok(out)
            }
            Err(_) => {
                self.tc.restore(snap);
                st.sol = sol;
                Ok(vec![g])
            }
        }
    }

    fn sort_level_of(&mut self, ty: &T, span: Span) -> R<Level> {
        let s = from_kernel(self.tc.infer(ty), span)?;
        let l = from_kernel(self.tc.ensure_sort(&s), span)?;
        Ok(self.tc.zonk_level(&l))
    }

    fn close_by_hyp(&mut self, st: &mut Tac, g: &Goal) -> bool {
        let tgt = self.tc.zonk(&g.target);
        for (_, v) in g.scope.iter().rev() {
            if let Term::FVar(id) = &**v {
                if let Ok(ty) = self.tc.local_ty(*id) {
                    if self.def_eq(&ty, &tgt) {
                        self.solve(st, g, v.clone());
                        return true;
                    }
                }
            }
        }
        false
    }

    fn t_intro(&mut self, st: &mut Tac, g: Goal, names: &[Ident], span: Span) -> R<Vec<Goal>> {
        let default = [Ident {
            name: "h".into(),
            span,
        }];
        let names = if names.is_empty() {
            &default[..]
        } else {
            names
        };
        let mut fvs = Vec::new();
        let mut target = self.tc.zonk(&g.target);
        let mut scope = g.scope.clone();
        for n in names {
            let w = match &*target {
                Term::Pi(..) => target.clone(),
                _ => from_kernel(self.tc.whnf(&target), n.span)?,
            };
            let Term::Pi(m, dom, body) = &*w else {
                return err(
                    n.span,
                    "`intro` needs a goal that is an implication or a function type",
                );
            };
            let fv = self.tc.fresh(&n.name, dom.clone(), *m);
            fvs.push(fv);
            scope.push((n.name.clone(), fvar(fv)));
            target = instantiate(body, &fvar(fv));
        }
        let mut ng = self.new_goal(&g, target, "");
        ng.scope = scope;
        st.sol.insert(g.mv, Sol::Lam(fvs, ng.mv));
        Ok(vec![ng])
    }

    /// `apply f`: unify the conclusion of `f`'s type (after some arguments) with the goal.
    fn apply_term(&mut self, st: &mut Tac, g: &Goal, f: T, span: Span) -> R<Vec<Goal>> {
        let tgt = self.tc.zonk(&g.target);
        let fty0 = from_kernel(self.tc.infer(&f), span)?;
        let mut limit = 0;
        loop {
            let snap = self.tc.snapshot();
            let mut term = f.clone();
            let mut ty = self.tc.zonk(&fty0);
            let mut args = Vec::new();
            let mut ok = true;
            for _ in 0..limit {
                let w = match &*ty {
                    Term::Pi(..) => ty.clone(),
                    _ => from_kernel(self.tc.whnf(&ty), span)?,
                };
                match &*w {
                    Term::Pi(_, dom, body) => {
                        let a = self.new_mvar(dom.clone(), span);
                        term = app(term, a.clone());
                        ty = instantiate(body, &a);
                        args.push(a);
                    }
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                self.tc.restore(snap);
                return err(
                    span,
                    format!(
                        "`apply` failed: cannot unify the conclusion of `{}` with the goal `{}`",
                        self.pp(&f),
                        self.pp(&tgt)
                    ),
                );
            }
            if matches!(self.tc.is_def_eq(&ty, &tgt), Ok(true)) {
                self.solve_goals(false)?;
                let mut out = Vec::new();
                for a in &args {
                    if let Term::MVar(_) = &*self.tc.zonk(a) {
                        let dom = from_kernel(self.tc.infer(a), span)?;
                        let dom = self.tc.zonk(&dom);
                        out.push(Goal {
                            mv: mvar_id(a),
                            scope: g.scope.clone(),
                            target: dom,
                            tag: g.tag.clone(),
                        });
                    }
                }
                self.solve(st, g, term);
                return Ok(out);
            }
            self.tc.restore(snap);
            limit += 1;
            if limit > 32 {
                return err(
                    span,
                    format!(
                        "`apply` failed: cannot unify the conclusion of `{}` with the goal `{}`",
                        self.pp(&f),
                        self.pp(&tgt)
                    ),
                );
            }
        }
    }

    fn t_constructor(&mut self, st: &mut Tac, g: Goal, span: Span) -> R<Vec<Goal>> {
        let tgt = self.tc.zonk(&g.target);
        let w = from_kernel(self.tc.whnf(&tgt), span)?;
        let (h, _) = app_spine(&w);
        let Term::Const(n, _) = &*h else {
            return err(
                span,
                "`constructor` needs a goal that is an inductive proposition",
            );
        };
        let ctor = match self.env.get(n) {
            Some(Decl::Inductive(i)) if i.ctors.len() == 1 => i.ctors[0].to_string(),
            Some(Decl::Inductive(i)) if i.ctors.len() > 1 => {
                return err(
                    span,
                    format!("`{n}` has several constructors; use `left`/`right` or `apply`"),
                )
            }
            _ => {
                return err(
                    span,
                    "`constructor` needs a goal that is an inductive proposition",
                )
            }
        };
        let (c, _) = self.const_term(&ctor);
        self.apply_term(st, &g, c, span)
    }

    fn t_contradiction(&mut self, st: &mut Tac, g: Goal, span: Span) -> R<Vec<Goal>> {
        let tgt = self.tc.zonk(&g.target);
        let lvl = self.sort_level_of(&tgt, span)?;
        let elim = cnst("False.elim".into(), vec![lvl]);
        let hyps: Vec<(T, T)> = g
            .scope
            .iter()
            .filter_map(|(_, v)| match &**v {
                Term::FVar(id) => self
                    .tc
                    .local_ty(*id)
                    .ok()
                    .map(|ty| (v.clone(), self.tc.zonk(&ty))),
                _ => None,
            })
            .collect();
        for (v, ty) in &hyps {
            // a hypothesis `False`
            let w = from_kernel(self.tc.whnf(ty), span)?;
            if matches!(&*w, Term::Const(n, _) if &**n == "False") {
                let pf = mk_apps(&elim, &[tgt.clone(), v.clone()]);
                self.solve(st, &g, pf);
                return Ok(vec![]);
            }
            // a hypothesis `C1 .. = C2 ..` between different constructors
            if let Some(pf) = self.discriminate(v, ty, span)? {
                self.solve(st, &g, mk_apps(&elim, &[tgt.clone(), pf]));
                return Ok(vec![]);
            }
            // a hypothesis `P -> False` together with a hypothesis `P`
            if let Term::Pi(_, p, q) = &*w {
                if matches!(&**q, Term::Const(n, _) if &**n == "False") {
                    for (v2, ty2) in &hyps {
                        if self.def_eq(ty2, p) {
                            let pf = mk_apps(&elim, &[tgt.clone(), app(v.clone(), v2.clone())]);
                            self.solve(st, &g, pf);
                            return Ok(vec![]);
                        }
                    }
                }
            }
        }
        err(span, "`contradiction` failed: no contradictory hypotheses")
    }

    /// A proof of a closed decidable proposition, by evaluation.
    fn decide(&mut self, p: &T, span: Span) -> R<T> {
        let w = from_kernel(self.tc.whnf(p), span)?;
        let (h, args) = app_spine(&w);
        let Term::Const(n, ls) = &*h else {
            return err(span, format!("`decide` cannot decide `{}`", self.pp(p)));
        };
        match (&**n, args.len()) {
            ("True", 0) => Ok(cnst("True.intro".into(), vec![])),
            ("And", 2) => {
                let l = self.decide(&args[0], span)?;
                let r = self.decide(&args[1], span)?;
                Ok(mk_apps(
                    &cnst("And.intro".into(), vec![]),
                    &[args[0].clone(), args[1].clone(), l, r],
                ))
            }
            ("Or", 2) => {
                if let Ok(l) = self.decide(&args[0], span) {
                    return Ok(mk_apps(
                        &cnst("Or.inl".into(), vec![]),
                        &[args[0].clone(), args[1].clone(), l],
                    ));
                }
                let r = self.decide(&args[1], span)?;
                Ok(mk_apps(
                    &cnst("Or.inr".into(), vec![]),
                    &[args[0].clone(), args[1].clone(), r],
                ))
            }
            ("Eq", 3) => {
                if self.def_eq(&args[1], &args[2]) {
                    Ok(mk_apps(
                        &cnst("Eq.refl".into(), ls.clone()),
                        &[args[0].clone(), args[1].clone()],
                    ))
                } else {
                    err(span, format!("`decide` failed: `{}` is false", self.pp(p)))
                }
            }
            _ => err(span, format!("`decide` cannot decide `{}`", self.pp(p))),
        }
    }

    fn unfold_in(&mut self, t: &T, name: &Ident) -> R<T> {
        let Some(Res::Global(kn)) = self.resolve(&name.name) else {
            return err(name.span, format!("unknown definition `{}`", name.name));
        };
        let Some(Decl::Def { lparams, val, .. }) = self.env.get(&kn).cloned() else {
            return err(name.span, format!("`{}` is not a definition", name.name));
        };
        let r = unfold_const(t, &kn, &|ls| instantiate_levels(&val, &lparams, ls));
        if &r == t {
            return err(
                name.span,
                format!("`unfold`: `{}` does not occur in the goal", name.name),
            );
        }
        Ok(r)
    }

    // ---- rewriting ----

    /// Open `∀ args, lhs = rhs` with a metavariable per argument.
    fn open_rule(&mut self, h: &T, span: Span) -> R<OpenRule> {
        let mut ty = from_kernel(self.tc.infer(h), span)?;
        let mut proof = h.clone();
        let mut args = Vec::new();
        loop {
            ty = self.tc.zonk(&ty);
            match &*ty {
                Term::Pi(_, dom, body) => {
                    let a = self.new_mvar(dom.clone(), span);
                    proof = app(proof, a.clone());
                    ty = instantiate(body, &a);
                    args.push(a);
                }
                _ => break,
            }
        }
        match self.eq_parts(&ty) {
            Some((level, alpha, lhs, rhs)) => Ok(OpenRule {
                proof,
                args,
                level,
                alpha,
                lhs,
                rhs,
            }),
            None => err(
                span,
                format!(
                    "`{}` is not an equation, so it cannot rewrite",
                    self.pp(&ty)
                ),
            ),
        }
    }

    /// First-order matching of a rewrite pattern against a term. Only metavariable
    /// positions may be filled in; computation is not used to make a pattern match
    /// (otherwise `n * succ(m)` would match `0 * a` because both reduce).
    fn match_pat(&mut self, p: &T, t: &T) -> bool {
        let p = self.tc.zonk(p);
        if matches!(&*p, Term::MVar(_)) || first_mvar(&p).is_none() {
            return self.def_eq(&p, t);
        }
        let (ph, pargs) = app_spine(&p);
        if let (Term::Const(n, _), Term::Lit(k)) = (&*ph, &**t) {
            if &**n == "Nat.succ" && pargs.len() == 1 && *k > 0 {
                return self.match_pat(&pargs[0], &lit(k - 1));
            }
        }
        let (th, targs) = app_spine(t);
        if pargs.len() != targs.len() {
            return false;
        }
        let heads_match = match (&*ph, &*th) {
            (Term::Const(a, _), Term::Const(b, _)) => a == b && self.def_eq(&ph, &th),
            (Term::FVar(a), Term::FVar(b)) => a == b,
            _ => false,
        };
        if !heads_match {
            return false;
        }
        for (pa, ta) in pargs.iter().zip(&targs) {
            if !self.match_pat(pa, ta) {
                return false;
            }
        }
        true
    }

    /// The first subterm of `target` that matches `pattern` (assigning its
    /// metavariables).
    fn find_instance(&mut self, pattern: &T, target: &T) -> Option<T> {
        let (ph, pargs) = app_spine(pattern);
        if matches!(&*ph, Term::MVar(_)) {
            return None;
        }
        let mut subs = Vec::new();
        collect_subterms(target, &mut subs);
        for s in subs {
            let (sh, sargs) = app_spine(&s);
            if sargs.len() != pargs.len() || sh != ph {
                continue;
            }
            let snap = self.tc.snapshot();
            if self.match_pat(pattern, &s) {
                return Some(s);
            }
            self.tc.restore(snap);
        }
        None
    }

    /// Rewrite the goal with one instance of the rule. Returns the new goal and the
    /// proof obligations the rule's hypotheses left over.
    fn rewrite_once(
        &mut self,
        st: &mut Tac,
        g: &Goal,
        rule: &OpenRule,
        rev: bool,
        at: Option<&Ident>,
        span: Span,
    ) -> R<Option<(Goal, Vec<Goal>)>> {
        // the type being rewritten: the goal, or a hypothesis
        let hyp = match at {
            Some(h) => {
                let pos = g
                    .scope
                    .iter()
                    .rposition(|(n, _)| plain_name(n) == h.name)
                    .ok_or_else(|| {
                        ElabError::new(h.span, format!("unknown hypothesis `{}`", h.name))
                    })?;
                let Term::FVar(id) = &*g.scope[pos].1 else {
                    return err(h.span, format!("`{}` is not a hypothesis", h.name));
                };
                Some((pos, *id, h.name.clone()))
            }
            None => None,
        };
        let tgt = match &hyp {
            Some((_, id, _)) => {
                let ty = from_kernel(self.tc.local_ty(*id), span)?;
                self.tc.zonk(&ty)
            }
            None => self.tc.zonk(&g.target),
        };
        let (pat, rep) = if rev {
            (&rule.rhs, &rule.lhs)
        } else {
            (&rule.lhs, &rule.rhs)
        };
        let pat0 = self.tc.zonk(pat);
        let Some(inst) = self.find_instance(&pat0, &tgt) else {
            return Ok(None);
        };
        let inst = self.tc.zonk(&inst);
        let pat = self.tc.zonk(pat);
        let rep = self.tc.zonk(rep);
        let body = replace_term(&tgt, &inst, 0);
        let new_target = instantiate(&body, &rep);
        if new_target == tgt {
            return Ok(None);
        }
        let alpha = self.tc.zonk(&rule.alpha);
        let motive = lam(Mult::Omega, alpha.clone(), body);
        let proof = self.tc.zonk(&rule.proof);
        if let Some((pos, id, name)) = hyp {
            // hypothesis `h : motive pat` becomes `h : motive rep`, using `pat = rep`
            let pe = if rev {
                mk_apps(
                    &cnst("Eq.symm".into(), vec![rule.level.clone()]),
                    &[alpha.clone(), rep.clone(), pat.clone(), proof],
                )
            } else {
                proof
            };
            let new_h = self.tc.fresh(&name, new_target, Mult::Omega);
            let mut ng = self.new_goal(g, g.target.clone(), "");
            ng.scope[pos] = (name, fvar(new_h));
            let term_h = mk_apps(
                &cnst("Eq.subst".into(), vec![rule.level.clone()]),
                &[alpha, pat, rep, motive, pe, fvar(id)],
            );
            if let Err(e) = self.tc.infer(&term_h) {
                return err(
                    span,
                    format!("rewrite produced an ill-typed motive: {}", e.0),
                );
            }
            let new_ty = from_kernel(self.tc.local_ty(new_h), span)?;
            let lam_mv = self.tc.new_mvar(pi(Mult::Omega, new_ty, g.target.clone()));
            st.sol
                .insert(mvar_id(&lam_mv), Sol::Lam(vec![new_h], ng.mv));
            let side = self.side_goals(g, rule, span)?;
            self.solve(st, g, app(lam_mv, term_h));
            return Ok(Some((ng, side)));
        }
        // goal = motive pat, from motive rep, with `rep = pat`
        let qp = if rev {
            proof
        } else {
            mk_apps(
                &cnst("Eq.symm".into(), vec![rule.level.clone()]),
                &[alpha.clone(), pat.clone(), rep.clone(), proof],
            )
        };
        let ng = self.new_goal(g, new_target, "");
        let term = mk_apps(
            &cnst("Eq.subst".into(), vec![rule.level.clone()]),
            &[alpha, rep, pat, motive, qp, mvar(ng.mv)],
        );
        if let Err(e) = self.tc.infer(&term) {
            return err(
                span,
                format!("rewrite produced an ill-typed motive: {}", e.0),
            );
        }
        let side = self.side_goals(g, rule, span)?;
        self.solve(st, g, term);
        Ok(Some((ng, side)))
    }

    /// The hypotheses of a conditional rewrite rule that unification left open.
    fn side_goals(&mut self, g: &Goal, rule: &OpenRule, span: Span) -> R<Vec<Goal>> {
        let mut side = Vec::new();
        for a in &rule.args {
            if let Term::MVar(_) = &*self.tc.zonk(a) {
                let dom = from_kernel(self.tc.infer(a), span)?;
                let dom = self.tc.zonk(&dom);
                side.push(Goal {
                    mv: mvar_id(a),
                    scope: g.scope.clone(),
                    target: dom,
                    tag: g.tag.clone(),
                });
            }
        }
        Ok(side)
    }

    fn t_rw(
        &mut self,
        st: &mut Tac,
        g: Goal,
        rules: &[(bool, Expr)],
        at: Option<&Ident>,
        span: Span,
    ) -> R<Vec<Goal>> {
        let mut cur = g;
        let mut sides = Vec::new();
        for (rev, e) in rules {
            let h = self.elab_in_goal(e, None)?;
            let rule = self.open_rule(&h, e.span)?;
            match self.rewrite_once(st, &cur, &rule, *rev, at, e.span)? {
                Some((ng, side)) => {
                    cur = ng;
                    sides.extend(side);
                }
                None => {
                    let pat = if *rev { &rule.rhs } else { &rule.lhs };
                    return err(
                        e.span,
                        format!(
                            "`rw` failed: did not find an instance of the pattern `{}` in {}",
                            self.pp(pat),
                            if at.is_some() {
                                "the hypothesis"
                            } else {
                                "the goal"
                            }
                        ),
                    );
                }
            }
        }
        let _ = span;
        if at.is_none() && self.try_rfl(st, &cur) {
            return Ok(sides);
        }
        let mut out = vec![cur];
        out.extend(sides);
        Ok(out)
    }

    fn t_simp(
        &mut self,
        st: &mut Tac,
        g: Goal,
        lemmas: &[Expr],
        at: Option<&Ident>,
        opts: SimpOpts,
        span: Span,
    ) -> R<Vec<Goal>> {
        enum Rule {
            Term(T),
            Global(String),
            Unfold(Ident),
        }
        let mut rules: Vec<Rule> = Vec::new();
        for e in lemmas {
            if let Some(p) = path_name(e) {
                if let Some(Res::Global(kn)) = self.resolve(&p) {
                    if matches!(self.env.get(&kn), Some(Decl::Def { .. }))
                        && !self.is_theorem_const(&kn)
                    {
                        rules.push(Rule::Unfold(Ident {
                            name: p,
                            span: e.span,
                        }));
                        continue;
                    }
                }
            }
            rules.push(Rule::Term(self.elab_in_goal(e, None)?));
        }
        if opts.all_hyps {
            for (_, v) in g.scope.iter().rev() {
                if let Term::FVar(id) = &**v {
                    if let Ok(ty) = self.tc.local_ty(*id) {
                        let ty = self.tc.zonk(&ty);
                        if matches!(&*app_spine(&ty).0, Term::Const(n, _) if &**n == "Eq") {
                            rules.push(Rule::Term(v.clone()));
                        }
                    }
                }
            }
        }
        if !opts.only {
            for name in self.tables.simp.clone() {
                rules.push(Rule::Global(name));
            }
        }
        let mut cur = g;
        let mut progress = false;
        if let Some(h) = at {
            // simplify a hypothesis; a hypothesis that becomes `False` closes the goal
            let mut sides = Vec::new();
            for _ in 0..500 {
                let mut next = None;
                for r in &rules {
                    let hterm = match r {
                        Rule::Term(h) => h.clone(),
                        Rule::Global(n) => self.const_term(n).0,
                        Rule::Unfold(_) => continue,
                    };
                    let snap = self.tc.snapshot();
                    let rule = self.open_rule(&hterm, span)?;
                    if let Some((ng, side)) =
                        self.rewrite_once(st, &cur, &rule, false, Some(h), span)?
                    {
                        let determined = rule
                            .args
                            .iter()
                            .all(|a| !matches!(&*self.tc.zonk(a), Term::MVar(_)));
                        if determined && side.is_empty() {
                            next = Some(ng);
                            break;
                        }
                        for s in &side {
                            st.sol.remove(&s.mv);
                        }
                    }
                    self.tc.restore(snap);
                }
                match next {
                    Some(ng) => {
                        cur = ng;
                        progress = true;
                    }
                    None => break,
                }
            }
            if !progress {
                return err(span, "`simp` made no progress");
            }
            let hv = cur
                .scope
                .iter()
                .rev()
                .find(|(n, _)| plain_name(n) == h.name)
                .map(|(_, v)| v.clone());
            if let Some(hv) = hv {
                if let Term::FVar(id) = &*hv {
                    let ty = from_kernel(self.tc.local_ty(*id), span)?;
                    let w = from_kernel(self.tc.whnf(&ty), span)?;
                    if matches!(&*w, Term::Const(n, _) if &**n == "False") {
                        let tgt = self.tc.zonk(&cur.target);
                        let lvl = self.sort_level_of(&tgt, span)?;
                        let pf = mk_apps(&cnst("False.elim".into(), vec![lvl]), &[tgt, hv]);
                        self.solve(st, &cur, pf);
                        return Ok(sides);
                    }
                }
            }
            sides.insert(0, cur);
            return Ok(sides);
        }
        for _ in 0..500 {
            if self.try_rfl(st, &cur) {
                return Ok(vec![]);
            }
            if matches!(self.tc.whnf(&cur.target).as_deref(), Ok(Term::Const(n, _)) if &**n == "True")
            {
                self.solve(st, &cur, cnst("True.intro".into(), vec![]));
                return Ok(vec![]);
            }
            let mut next = None;
            for r in &rules {
                match r {
                    Rule::Unfold(n) => {
                        // `simp [f]`: evaluate one call of `f`, as far as it reduces cleanly
                        let tgt = self.tc.zonk(&cur.target);
                        let kn = match self.resolve(&n.name) {
                            Some(Res::Global(kn)) => kn,
                            _ => continue,
                        };
                        if let Some(t2) = self.eval_step_named(&tgt, Some(&kn)) {
                            let ng = self.new_goal(&cur, t2, "");
                            self.solve(st, &cur, mvar(ng.mv));
                            next = Some(ng);
                            break;
                        }
                    }
                    Rule::Term(_) | Rule::Global(_) => {
                        let snap = self.tc.snapshot();
                        let h = match r {
                            Rule::Term(h) => h.clone(),
                            Rule::Global(n) => self.const_term(n).0,
                            Rule::Unfold(_) => unreachable!(),
                        };
                        let rule = self.open_rule(&h, span)?;
                        // try the rule left to right
                        if let Some((ng, side)) =
                            self.rewrite_once(st, &cur, &rule, false, None, span)?
                        {
                            // a conditional rule fires when its side conditions (propositions)
                            // can be discharged; an undetermined data argument rejects it
                            let mut ok = true;
                            for s in &side {
                                if !self.is_prop_type(&s.target) || !self.discharge(st, s, span) {
                                    ok = false;
                                    break;
                                }
                            }
                            if ok {
                                next = Some(ng);
                                break;
                            }
                            for s in &side {
                                st.sol.remove(&s.mv);
                            }
                        }
                        self.tc.restore(snap);
                    }
                }
            }
            if next.is_none() {
                let tgt = self.tc.zonk(&cur.target);
                // iota: a recursor (or `if`) whose major premise became a constructor
                let reduced = self.reduce_recs(&tgt, 0);
                let step = if reduced != tgt {
                    Some(reduced)
                } else {
                    self.eval_step(&tgt)
                };
                if let Some(t2) = step {
                    let ng = self.new_goal(&cur, t2, "");
                    self.solve(st, &cur, mvar(ng.mv));
                    next = Some(ng);
                }
            }
            match next {
                Some(ng) => {
                    cur = ng;
                    progress = true;
                }
                None => break,
            }
        }
        if self.try_rfl(st, &cur) || self.close_by_hyp(st, &cur) {
            return Ok(vec![]);
        }
        if !progress {
            return err(span, "`simp` made no progress");
        }
        Ok(vec![cur])
    }

    /// Evaluate a call of a user function whose arguments are constructors: unfold the
    /// definition and reduce (beta, iota) until a constructor or another function
    /// shows. Stuck results (a recursor waiting for a variable) are rejected, so the
    /// goal never fills up with recursor terms.
    fn eval_head(&mut self, s: &T) -> Option<T> {
        let mut cur = s.clone();
        for _ in 0..32 {
            let (h, args) = app_spine(&cur);
            let Term::Const(n, ls) = &*h else { break };
            if matches!(&**n, "Nat.add" | "Nat.mul") || self.is_theorem_const(n) {
                break;
            }
            let Some(Decl::Def { lparams, val, .. }) = self.env.get(n).cloned() else {
                break;
            };
            if lparams.len() != ls.len() {
                break;
            }
            self.pending_call = cur.clone();
            let unfolded = head_beta(&mk_apps(&instantiate_levels(&val, &lparams, ls), &args));
            let next = self.tc.whnf_core(&unfolded).ok()?;
            let next = self.reduce_recs(&next, 0);
            // recursive calls of the function come out as recursor applications: fold them back
            let next = self.refold_calls(&next, &h, args.len(), 0);
            let (nh, _) = app_spine(&next);
            // an unfolding that gets stuck on a variable is not wanted: keep the call
            if matches!(&*nh, Term::Lam(..) | Term::MVar(_)) || self.mentions_rec(&next) {
                break;
            }
            cur = next;
        }
        (cur != *s).then_some(cur)
    }

    /// Turn recursor applications that are recursive calls of `f` back into calls:
    /// `Rec params motive minors major others` is `f` applied with the major premise at
    /// the position of the decreasing parameter. Found by trying each position and
    /// checking definitional equality, so wrong guesses are harmless.
    fn refold_calls(&mut self, t: &T, f: &T, nargs: usize, depth: u32) -> T {
        if depth > 64 {
            return t.clone();
        }
        match &**t {
            Term::App(..) => {
                let (h, args) = app_spine(t);
                let args: Vec<T> = args
                    .iter()
                    .map(|a| self.refold_calls(a, f, nargs, depth + 1))
                    .collect();
                let me = mk_apps(&h, &args);
                if let Term::Const(n, _) = &*h {
                    if let Some(Decl::Rec(r)) = self.env.get(n).cloned() {
                        let prefix = r.nparams + r.nmotives + r.nminors + r.nindices;
                        if args.len() > prefix {
                            let e = args.len() - prefix; // major premise and the other parameters
                            if let Some(ngen) = nargs.checked_sub(e) {
                                let (_, orig) = app_spine(&self.pending_call);
                                if orig.len() == nargs {
                                    let major = args[prefix].clone();
                                    let others = &args[prefix + 1..];
                                    for k in 0..e {
                                        let mut explicit: Vec<T> = others.to_vec();
                                        explicit.insert(k, major.clone());
                                        let cand =
                                            mk_apps(f, &[orig[..ngen].to_vec(), explicit].concat());
                                        if self.def_eq(&cand, &me) {
                                            return cand;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                me
            }
            Term::Lam(m, ty, b) => lam(
                *m,
                self.refold_calls(ty, f, nargs, depth + 1),
                self.refold_calls(b, f, nargs, depth + 1),
            ),
            _ => t.clone(),
        }
    }

    /// Reduce recursor applications inside a term (innermost first) where their
    /// major premise is a constructor.
    fn reduce_recs(&mut self, t: &T, depth: u32) -> T {
        if depth > 64 {
            return t.clone();
        }
        match &**t {
            Term::App(..) => {
                let (f, args) = app_spine(t);
                let f2 = self.reduce_recs(&f, depth + 1);
                let args2: Vec<T> = args
                    .iter()
                    .map(|a| self.reduce_recs(a, depth + 1))
                    .collect();
                let t2 = mk_apps(&f2, &args2);
                if let Term::Const(n, _) = &*f2 {
                    if matches!(self.env.get(n), Some(Decl::Rec(_))) {
                        if let Ok(r) = self.tc.whnf_core(&t2) {
                            if r != t2 {
                                return self.reduce_recs(&r, depth + 1);
                            }
                        }
                    }
                }
                t2
            }
            Term::Lam(m, ty, b) => lam(
                *m,
                self.reduce_recs(ty, depth + 1),
                self.reduce_recs(b, depth + 1),
            ),
            _ => t.clone(),
        }
    }

    /// Does the term contain a recursor? (A call of a recursive function on an open
    /// term unfolds into one; such results are not wanted in the goal.)
    fn mentions_rec(&self, t: &T) -> bool {
        match &**t {
            // `if` is `Bool.rec`: a stuck condition is fine, a rewrite can still decide it
            Term::Const(n, _) => {
                &**n != "Bool.rec" && matches!(self.env.get(n), Some(Decl::Rec(_)))
            }
            Term::App(f, a) => self.mentions_rec(f) || self.mentions_rec(a),
            Term::Lam(_, ty, b) | Term::Pi(_, ty, b) => {
                self.mentions_rec(ty) || self.mentions_rec(b)
            }
            Term::Let(_, ty, v, b) => {
                self.mentions_rec(ty) || self.mentions_rec(v) || self.mentions_rec(b)
            }
            _ => false,
        }
    }

    /// One evaluation step somewhere inside `t`: the new type, if any.
    fn eval_step(&mut self, t: &T) -> Option<T> {
        self.eval_step_named(t, None)
    }

    /// Like `eval_step`, restricted to calls of one function.
    fn eval_step_named(&mut self, t: &T, only: Option<&str>) -> Option<T> {
        let mut subs = Vec::new();
        collect_subterms(t, &mut subs);
        for s in subs {
            let (h, args) = app_spine(&s);
            let Term::Const(n, _) = &*h else { continue };
            if only.is_some_and(|o| &**n != o) {
                continue;
            }
            if args.is_empty() || !matches!(self.env.get(n), Some(Decl::Def { .. })) {
                continue;
            }
            // predicates such as `le` and `lt` stay folded: tactics recognize them by name
            if let Ok(sort_of) = self.tc.infer(&s) {
                if matches!(self.tc.whnf(&sort_of).as_deref(), Ok(Term::Sort(l)) if l.is_zero()) {
                    continue;
                }
            }
            if let Some(w) = self.eval_head(&s) {
                let body = replace_term(t, &s, 0);
                return Some(instantiate(&body, &w));
            }
        }
        None
    }

    fn is_prop_type(&mut self, ty: &T) -> bool {
        let ty = self.tc.zonk(ty);
        match self.tc.infer(&ty).and_then(|s| self.tc.ensure_sort(&s)) {
            Ok(l) => self.tc.zonk_level(&l).is_zero(),
            Err(_) => false,
        }
    }

    /// Prove a side condition of a conditional rewrite rule from the context.
    fn discharge(&mut self, st: &mut Tac, g: &Goal, span: Span) -> bool {
        if self.close_by_hyp(st, g) || self.try_rfl(st, g) {
            return true;
        }
        if self.env.get("omega_sound").is_some() {
            let snap = self.tc.snapshot();
            if self.t_omega(st, g.clone(), span).is_ok() {
                return true;
            }
            self.tc.restore(snap);
        }
        false
    }

    fn is_theorem_const(&mut self, name: &str) -> bool {
        // a definition whose type is a proposition is a theorem
        match self.env.get(name) {
            Some(d) => {
                let ty = d.ty().clone();
                let mut tc = TypeChecker::new(self.env);
                match tc.telescope(&ty, None) {
                    Ok((_, concl)) => match tc.infer(&concl).and_then(|s| tc.ensure_sort(&s)) {
                        Ok(l) => l.is_zero(),
                        Err(_) => false,
                    },
                    Err(_) => false,
                }
            }
            None => false,
        }
    }

    // ---- induction and case analysis ----

    #[allow(clippy::too_many_arguments)]
    fn t_induct(
        &mut self,
        st: &mut Tac,
        g: Goal,
        var: &Ident,
        generalizing: &[Ident],
        arms: Option<&[CaseArm]>,
        with_ih: bool,
        span: Span,
    ) -> R<Vec<Goal>> {
        // indices that are not variables (`h : Even(1)`) are replaced by fresh variables
        // with an equation, which each case then carries as a hypothesis `heq_i`
        if let Some((ng, nvar)) = self.generalize_indices(st, &g, var, span)? {
            return self.t_induct(st, ng, &nvar, generalizing, arms, with_ih, span);
        }
        // hypotheses that mention the variable are reverted too, and put back in each case
        let mut to_revert: Vec<Ident> = generalizing.to_vec();
        if let Some(Term::FVar(xid)) = g
            .scope
            .iter()
            .rfind(|(n, _)| plain_name(n) == var.name)
            .map(|(_, v)| &**v)
        {
            // hypotheses that mention the variable or the indices of its type
            let mut roots = vec![*xid];
            if let Ok(xty) = self.tc.local_ty(*xid) {
                let xty = self.tc.zonk(&xty);
                if let Ok(w) = self.tc.whnf(&xty) {
                    let (h, targs) = app_spine(&w);
                    if let Term::Const(n, _) = &*h {
                        if let Some(Decl::Inductive(info)) = self.env.get(n) {
                            for t in targs.iter().skip(info.nparams) {
                                if let Term::FVar(i) = &**t {
                                    roots.push(*i);
                                }
                            }
                        }
                    }
                }
            }
            for (n, v) in &g.scope {
                if let Term::FVar(id) = &**v {
                    if !roots.contains(id)
                        && self.tc.local_ty(*id).is_ok_and(|ty| {
                            let ty = self.tc.zonk(&ty);
                            roots.iter().any(|r| contains_fvar(&ty, *r))
                        })
                        && !to_revert.iter().any(|r| r.name == plain_name(n))
                    {
                        to_revert.push(Ident {
                            name: plain_name(n).to_string(),
                            span: var.span,
                        });
                    }
                }
            }
        }
        if !to_revert.is_empty() {
            let (g2, names) = self.revert_vars(st, &g, &to_revert, span)?;
            return self.t_induct_core(st, g2, var, arms, with_ih, &names, span);
        }
        self.t_induct_core(st, g, var, arms, with_ih, &[], span)
    }

    /// `h : I params t` with some index `t` not a (distinct) variable becomes
    /// `∀ j, ∀ h' : I params j, j = t → goal`, introduced as `idx_i`, `hx`, `heq_i`.
    fn generalize_indices(
        &mut self,
        st: &mut Tac,
        g: &Goal,
        var: &Ident,
        span: Span,
    ) -> R<Option<(Goal, Ident)>> {
        let Some((_, v)) = g.scope.iter().rfind(|(n, _)| plain_name(n) == var.name) else {
            return Ok(None);
        };
        let Term::FVar(xid) = &**v else {
            return Ok(None);
        };
        let xid = *xid;
        let Ok(xty) = self.tc.local_ty(xid) else {
            return Ok(None);
        };
        let xty = self.tc.zonk(&xty);
        let w = from_kernel(self.tc.whnf(&xty), span)?;
        let (h, targs) = app_spine(&w);
        let Term::Const(iname, ilevels) = &*h else {
            return Ok(None);
        };
        let Some(Decl::Inductive(info)) = self.env.get(iname).cloned() else {
            return Ok(None);
        };
        if info.nindices == 0 {
            return Ok(None);
        }
        let idxs = &targs[info.nparams..];
        let mut seen = Vec::new();
        let is_var = |t: &T, seen: &mut Vec<u32>| match &**t {
            Term::FVar(i) if *i != xid && !seen.contains(i) => {
                seen.push(*i);
                true
            }
            _ => false,
        };
        if idxs.iter().all(|t| is_var(t, &mut seen)) {
            return Ok(None);
        }
        let mut new_idxs = Vec::new();
        let mut js = Vec::new();
        let mut eqs = Vec::new();
        let mut seen = Vec::new();
        for (i, t) in idxs.iter().enumerate() {
            if is_var(t, &mut seen) {
                new_idxs.push(t.clone());
                continue;
            }
            let ty = from_kernel(self.tc.infer(t), span)?;
            let ty = self.tc.zonk(&ty);
            let lvl = self.sort_level_of(&ty, span)?;
            let j = self.tc.fresh(&format!("idx{i}"), ty.clone(), Mult::Omega);
            new_idxs.push(fvar(j));
            let eq = mk_apps(
                &cnst("Eq".into(), vec![lvl.clone()]),
                &[ty.clone(), fvar(j), t.clone()],
            );
            let e = self.tc.fresh(&format!("heq{i}"), eq, Mult::Omega);
            js.push((j, t.clone(), ty, lvl));
            eqs.push(e);
        }
        let hty = mk_apps(
            &cnst(iname.clone(), ilevels.clone()),
            &[targs[..info.nparams].to_vec(), new_idxs].concat(),
        );
        let hx = self.tc.fresh("hx", hty, Mult::Omega);
        self.tc.zonk_locals();
        let target = self.tc.zonk(&g.target);
        let binders: Vec<u32> = js
            .iter()
            .map(|(j, ..)| *j)
            .chain(std::iter::once(hx))
            .chain(eqs.iter().copied())
            .collect();
        let pi_ty = self.tc.mk_pi(&binders, &target);
        let ng = self.new_goal(g, pi_ty, "");
        let mut args: Vec<T> = js.iter().map(|(_, t, ..)| t.clone()).collect();
        args.push(fvar(xid));
        for (_, t, ty, lvl) in &js {
            args.push(mk_apps(
                &cnst("Eq.refl".into(), vec![lvl.clone()]),
                &[ty.clone(), t.clone()],
            ));
        }
        self.solve(st, g, mk_apps(&mvar(ng.mv), &args));
        let mut names: Vec<Ident> = Vec::new();
        for (k, (j, ..)) in js.iter().enumerate() {
            let _ = j;
            names.push(Ident {
                name: format!("idx{k}"),
                span,
            });
        }
        names.push(Ident {
            name: "hx".into(),
            span,
        });
        for k in 0..eqs.len() {
            names.push(Ident {
                name: format!("heq{k}"),
                span,
            });
        }
        let mut gs = self.t_intro(st, ng, &names, span)?;
        Ok(Some((
            gs.remove(0),
            Ident {
                name: "hx".into(),
                span,
            },
        )))
    }

    /// Put the hypotheses `names` (reverted before the split) back in a new case.
    fn reintro(&mut self, st: &mut Tac, g: Goal, names: &[String], span: Span) -> R<Goal> {
        if names.is_empty() {
            return Ok(g);
        }
        let idents: Vec<Ident> = names
            .iter()
            .map(|n| Ident {
                name: n.clone(),
                span,
            })
            .collect();
        let mut gs = self.t_intro(st, g, &idents, span)?;
        Ok(gs.remove(0))
    }

    /// `revert a b`: the goal becomes `∀ a b, goal`, together with everything that
    /// depends on `a` or `b`. Returns the new goal and the reverted names, oldest first.
    fn revert_vars(
        &mut self,
        st: &mut Tac,
        g: &Goal,
        names: &[Ident],
        span: Span,
    ) -> R<(Goal, Vec<String>)> {
        let mut ids: Vec<u32> = Vec::new();
        for n in names {
            let (_, v) = g
                .scope
                .iter()
                .rfind(|(m, _)| plain_name(m) == n.name)
                .ok_or_else(|| ElabError::new(n.span, format!("unknown variable `{}`", n.name)))?;
            match &**v {
                Term::FVar(id) => ids.push(*id),
                _ => return err(n.span, format!("`{}` cannot be reverted", n.name)),
            }
        }
        loop {
            let mut grew = false;
            for (_, v) in &g.scope {
                if let Term::FVar(id) = &**v {
                    if !ids.contains(id)
                        && self.tc.local_ty(*id).is_ok_and(|ty| {
                            let ty = self.tc.zonk(&ty);
                            ids.iter().any(|r| contains_fvar(&ty, *r))
                        })
                    {
                        ids.push(*id);
                        grew = true;
                    }
                }
            }
            if !grew {
                break;
            }
        }
        let mut fvs = Vec::new();
        let mut out_names = Vec::new();
        let mut scope = Vec::new();
        for (n, v) in &g.scope {
            match &**v {
                Term::FVar(id) if ids.contains(id) => {
                    fvs.push(*id);
                    out_names.push(plain_name(n).to_string());
                }
                _ => scope.push((n.clone(), v.clone())),
            }
        }
        self.tc.zonk_locals();
        let tgt = self.tc.zonk(&g.target);
        let new_target = self.tc.mk_pi(&fvs, &tgt);
        let mut ng = self.new_goal(g, new_target, "");
        ng.scope = scope;
        let args: Vec<T> = fvs.iter().map(|&f| fvar(f)).collect();
        self.solve(st, g, mk_apps(&mvar(ng.mv), &args));
        let _ = span;
        Ok((ng, out_names))
    }

    fn t_exists(&mut self, st: &mut Tac, g: Goal, e: &Expr, span: Span) -> R<Vec<Goal>> {
        let tgt = self.tc.zonk(&g.target);
        let w = from_kernel(self.tc.whnf(&tgt), span)?;
        let (h, args) = app_spine(&w);
        let (Term::Const(n, ls), 2) = (&*h, args.len()) else {
            return err(span, "`exists` needs a goal of the form `Exists(p)`");
        };
        if &**n != "Exists" {
            return err(span, "`exists` needs a goal of the form `Exists(p)`");
        }
        let witness = self.elab_in_goal(e, Some(&args[0]))?;
        let body = head_beta(&app(args[1].clone(), witness.clone()));
        let ng = self.new_goal(&g, body, "");
        let pf = mk_apps(
            &cnst("Exists.intro".into(), ls.clone()),
            &[args[0].clone(), args[1].clone(), witness, mvar(ng.mv)],
        );
        self.solve(st, &g, pf);
        if self.try_rfl(st, &ng) {
            return Ok(vec![]);
        }
        Ok(vec![ng])
    }

    #[allow(clippy::too_many_arguments)]
    fn t_induct_core(
        &mut self,
        st: &mut Tac,
        g: Goal,
        var: &Ident,
        arms: Option<&[CaseArm]>,
        with_ih: bool,
        reintro: &[String],
        span: Span,
    ) -> R<Vec<Goal>> {
        let what = if with_ih { "induction" } else { "cases" };
        let pos = g
            .scope
            .iter()
            .rposition(|(n, _)| plain_name(n) == var.name)
            .ok_or_else(|| ElabError::new(var.span, format!("unknown variable `{}`", var.name)))?;
        let xid = match &*g.scope[pos].1 {
            Term::FVar(id) => *id,
            _ => {
                return err(
                    var.span,
                    format!("`{what}` needs a local variable, `{}` is not one", var.name),
                )
            }
        };
        let xty = from_kernel(self.tc.local_ty(xid), var.span)?;
        let xty = self.tc.zonk(&xty);
        let w = from_kernel(self.tc.whnf(&xty), var.span)?;
        let (h, targs) = app_spine(&w);
        let (iname, ilevels) = match &*h {
            Term::Const(n, ls) => (n.to_string(), ls.clone()),
            _ => {
                return err(
                    var.span,
                    format!("`{what}`: `{}` does not have an inductive type", var.name),
                )
            }
        };
        let info = match self.env.get(&iname) {
            Some(Decl::Inductive(i)) => i.clone(),
            _ => {
                return err(
                    var.span,
                    format!("`{what}`: `{}` does not have an inductive type", var.name),
                )
            }
        };
        // the indices of an indexed family must be distinct variables: the motive
        // abstracts them (`cases h` on `h : a = b` needs `b` to be a variable)
        let idx_terms: Vec<T> = targs[info.nparams..].to_vec();
        let mut idx_fvs: Vec<u32> = Vec::new();
        for t in &idx_terms {
            match &**t {
                Term::FVar(i) if *i != xid && !idx_fvs.contains(i) => idx_fvs.push(*i),
                _ => {
                    return err(
                        var.span,
                        format!(
                            "`{what}`: the indices of `{}` must be distinct variables, found `{}`",
                            var.name,
                            self.pp(t)
                        ),
                    )
                }
            }
        }
        let rec_info = match self.env.get(&info.rec) {
            Some(Decl::Rec(r)) => r.clone(),
            _ => return err(span, "internal error: missing recursor"),
        };
        let target = self.tc.zonk(&g.target);
        let lvl = self.sort_level_of(&target, span)?;
        let rec_levels: Vec<Level> = if rec_info.lparams.len() == info.lparams.len() + 1 {
            let mut v = vec![lvl];
            v.extend(ilevels.iter().cloned());
            v
        } else {
            if !lvl.is_zero() {
                return err(
                    span,
                    format!("`{what}` on `{iname}` can only prove propositions"),
                );
            }
            ilevels.clone()
        };
        let params: Vec<T> = targs[..info.nparams].to_vec();
        self.tc.zonk_locals();
        let motive = self
            .tc
            .mk_lam(&[idx_fvs.clone(), vec![xid]].concat(), &target);
        // a mutual family: the other types get the constant `PUnit` motive
        let punit_lvl = if rec_levels.len() > info.lparams.len() {
            rec_levels[0].clone()
        } else {
            Level::Zero
        };
        let mut motives_all: Vec<T> = Vec::new();
        for fname in &info.family {
            if **fname == *iname {
                motives_all.push(motive.clone());
            } else {
                let fty = from_kernel(self.env.const_type(fname, &ilevels), span)?;
                let fty = from_kernel(self.tc.instantiate_pis(&fty, &params), span)?;
                let (fidx, _) = from_kernel(self.tc.telescope(&fty, None), span)?;
                if !fidx.is_empty() {
                    return err(
                        span,
                        format!("`{what}` on mutual indexed families is not supported"),
                    );
                }
                let kt = mk_apps(&cnst(fname.clone(), ilevels.clone()), &params);
                motives_all.push(lam(
                    Mult::Omega,
                    kt,
                    cnst("PUnit".into(), vec![punit_lvl.clone()]),
                ));
            }
        }
        debug_assert_eq!(motives_all.len(), rec_info.nmotives);
        let mut rty = from_kernel(self.env.const_type(&info.rec, &rec_levels), span)?;
        for p in params.iter().chain(motives_all.iter()) {
            match &*rty {
                Term::Pi(_, _, b) => rty = instantiate(b, p),
                _ => return err(span, "internal error: malformed recursor type"),
            }
        }
        // arms by constructor
        let ctor_short: Vec<String> = info.ctors.iter().map(|c| short(c).to_string()).collect();
        if let Some(arms) = arms {
            for a in arms {
                if !ctor_short.contains(&a.ctor.name) {
                    return err(
                        a.ctor.span,
                        format!("`{iname}` has no constructor `{}`", a.ctor.name),
                    );
                }
            }
            for c in &ctor_short {
                if !arms.iter().any(|a| &a.ctor.name == c) {
                    return err(span, format!("missing case `{c}`"));
                }
            }
        }
        let mut minors = Vec::new();
        let mut goals = Vec::new();
        let mut arm_goals = Vec::new();
        for fname in &info.family {
            if **fname != *iname {
                let nf = match self.env.get(fname) {
                    Some(Decl::Inductive(i)) => i.ctors.len(),
                    _ => return err(span, "internal error: missing family member"),
                };
                for _ in 0..nf {
                    let (dom, rest) = match &*rty {
                        Term::Pi(_, d, b) => (d.clone(), b.clone()),
                        _ => return err(span, "internal error: malformed recursor type"),
                    };
                    let (bs, _) = from_kernel(self.tc.telescope(&head_beta(&dom), None), span)?;
                    let unit = cnst("PUnit.unit".into(), vec![punit_lvl.clone()]);
                    let m = self.tc.mk_lam(&bs, &unit);
                    rty = instantiate(&rest, &m);
                    minors.push(m);
                }
                continue;
            }
            for (i, cname) in info.ctors.iter().enumerate() {
                let nfields = match self.env.get(cname) {
                    Some(Decl::Ctor(c)) => c.nfields,
                    _ => return err(span, "internal error: missing constructor"),
                };
                let (dom, rest) = match &*rty {
                    Term::Pi(_, d, b) => (d.clone(), b.clone()),
                    _ => return err(span, "internal error: malformed recursor type"),
                };
                let arm = arms.and_then(|a| a.iter().find(|a| a.ctor.name == ctor_short[i]));
                let given: Vec<String> = match arm {
                    Some(a) => a.binders.iter().map(|b| b.name.clone()).collect(),
                    // a dependent `match` names the binders of each case itself
                    None => self
                        .case_names
                        .as_ref()
                        .and_then(|m| m.get(&ctor_short[i]).cloned())
                        .unwrap_or_default(),
                };
                let mut fvs = Vec::new();
                let mut cur = dom.clone();
                let mut scope: Vec<(String, T)> = g
                    .scope
                    .iter()
                    .filter(|(_, v)| match &**v {
                        Term::FVar(i) => *i != xid && !idx_fvs.contains(i),
                        _ => true,
                    })
                    .cloned()
                    .collect();
                let mut k = 0;
                while let Term::Pi(m, d, b) = &*cur.clone() {
                    let is_ih = k >= nfields;
                    let name = match given.get(k) {
                        Some(n) => n.clone(),
                        None if is_ih => "ih".to_string(),
                        None => format!("x{}", k + 1),
                    };
                    let fv = self.tc.fresh(&name, head_beta(d), *m);
                    fvs.push(fv);
                    if !is_ih || with_ih {
                        scope.push((name, fvar(fv)));
                    }
                    cur = instantiate(b, &fvar(fv));
                    k += 1;
                }
                if let Some(a) = arm {
                    if a.binders.len() > if with_ih { k } else { nfields } {
                        return err(
                            a.ctor.span,
                            format!("`{}` binds too many names", a.ctor.name),
                        );
                    }
                }
                let new_target = head_beta(&self.tc.zonk(&cur));
                let mv = self.tc.new_mvar(new_target.clone());
                let sub = Goal {
                    mv: mvar_id(&mv),
                    scope,
                    target: new_target,
                    tag: ctor_short[i].clone(),
                };
                let sub_mv = sub.mv;
                let sub = self.reintro(st, sub, reintro, span)?;
                let lam_mv = self.tc.new_mvar(dom);
                st.sol.insert(mvar_id(&lam_mv), Sol::Lam(fvs, sub_mv));
                minors.push(lam_mv.clone());
                rty = instantiate(&rest, &lam_mv);
                match arm {
                    Some(a) => arm_goals.push((sub, a.body.clone())),
                    None => goals.push(sub),
                }
            }
        }
        let mut args = params;
        args.extend(motives_all);
        args.extend(minors);
        args.extend(idx_terms);
        args.push(fvar(xid));
        self.solve(st, &g, mk_apps(&cnst(info.rec.clone(), rec_levels), &args));
        for (sub, body) in arm_goals {
            self.focus(st, sub, &body, span)?;
        }
        Ok(goals)
    }
}
