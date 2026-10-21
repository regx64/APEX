//! The `omega` tactic: linear arithmetic over `Nat`, with a proof.
//!
//! Hypotheses and the negated goal become inequalities `lo ≤ hi` between linear
//! expressions in atoms (the non-arithmetic subterms). A contradiction is found by
//! Fourier–Motzkin elimination, which also yields the multipliers of a Farkas
//! certificate. The proof is `omega_sound cs ws env rfl rfl holds` from the verified
//! library in `prelude_omega.apex`: the kernel *recomputes* the certificate check, so
//! this search is untrusted. Case splits (`∨`, `≠`, truncated subtraction) are done on
//! the goal level, before the certificate search.

use super::*;
use std::collections::HashSet;

/// A linear expression over atoms, as the library's `LExpr`.
#[derive(Clone, Debug)]
enum Ex {
    Atom(usize),
    Const(u64),
    Add(Box<Ex>, Box<Ex>),
    Scale(u64, Box<Ex>),
    /// `e * c`
    ScaleR(Box<Ex>, u64),
}

/// `lo ≤ hi`, with a proof of `le lo hi` (up to definitional unfolding).
#[derive(Clone)]
struct Fact {
    lo: Ex,
    hi: Ex,
    proof: T,
}

#[derive(Default, Clone)]
pub(super) struct OmegaState {
    /// Hypotheses already case-split.
    done_hyps: HashSet<u32>,
    /// `a - b` atoms already case-split.
    done_subs: Vec<T>,
}

fn nat() -> T {
    cnst("Nat".into(), vec![])
}

fn c(name: &str) -> T {
    cnst(name.into(), vec![])
}

fn ex_term(e: &Ex) -> T {
    match e {
        Ex::Atom(i) => app(c("LExpr.Atom"), lit(*i as u64)),
        Ex::Const(n) => app(c("LExpr.Const"), lit(*n)),
        Ex::Add(a, b) => mk_apps(&c("LExpr.Add"), &[ex_term(a), ex_term(b)]),
        Ex::Scale(k, x) => mk_apps(&c("LExpr.Scale"), &[lit(*k), ex_term(x)]),
        Ex::ScaleR(x, k) => mk_apps(&c("LExpr.ScaleR"), &[ex_term(x), lit(*k)]),
    }
}

fn list_of(elem_ty: &T, items: &[T]) -> T {
    let lvl = vec![Level::zero()];
    let mut r = app(cnst("List.nil".into(), lvl.clone()), elem_ty.clone());
    for x in items.iter().rev() {
        r = mk_apps(
            &cnst("List.cons".into(), lvl.clone()),
            &[elem_ty.clone(), x.clone(), r],
        );
    }
    r
}

/// Coefficients and constant of an expression.
fn linear(e: &Ex, natoms: usize) -> (Vec<i128>, i128) {
    match e {
        Ex::Atom(i) => {
            let mut v = vec![0; natoms];
            v[*i] = 1;
            (v, 0)
        }
        Ex::Const(n) => (vec![0; natoms], *n as i128),
        Ex::Add(a, b) => {
            let (mut x, k1) = linear(a, natoms);
            let (y, k2) = linear(b, natoms);
            for (p, q) in x.iter_mut().zip(y) {
                *p += q;
            }
            (x, k1 + k2)
        }
        Ex::Scale(k, x) | Ex::ScaleR(x, k) => {
            let (mut v, c0) = linear(x, natoms);
            for p in v.iter_mut() {
                *p *= *k as i128;
            }
            (v, c0 * *k as i128)
        }
    }
}

fn gcd(a: i128, b: i128) -> i128 {
    if b == 0 {
        a.abs()
    } else {
        gcd(b, a % b)
    }
}

#[derive(Clone)]
struct Row {
    coef: Vec<i128>,
    k: i128,
    w: Vec<i128>,
}

impl Row {
    fn normalize(&mut self) {
        let mut g = self.k.abs();
        for x in self.coef.iter().chain(&self.w) {
            g = gcd(g, *x);
        }
        if g > 1 {
            for x in self.coef.iter_mut().chain(self.w.iter_mut()) {
                *x /= g;
            }
            self.k /= g;
        }
    }
}

/// Fourier–Motzkin elimination over the rationals, tracking how each derived row is a
/// nonnegative combination of the input facts. `Some(weights)` when a contradiction
/// `0 ≤ k < 0` is derived.
fn farkas(facts: &[Fact], natoms: usize) -> Option<Vec<i128>> {
    let n = facts.len();
    let mut rows: Vec<Row> = Vec::new();
    for (i, f) in facts.iter().enumerate() {
        let (lc, lk) = linear(&f.lo, natoms);
        let (hc, hk) = linear(&f.hi, natoms);
        let mut w = vec![0; n];
        w[i] = 1;
        rows.push(Row {
            coef: hc.iter().zip(&lc).map(|(h, l)| h - l).collect(),
            k: hk - lk,
            w,
        });
    }
    // atoms are natural numbers
    for j in 0..natoms {
        let mut coef = vec![0; natoms];
        coef[j] = 1;
        rows.push(Row {
            coef,
            k: 0,
            w: vec![0; n],
        });
    }
    loop {
        for r in rows.iter_mut() {
            r.normalize();
        }
        if let Some(r) = rows
            .iter()
            .find(|r| r.coef.iter().all(|x| *x == 0) && r.k < 0)
        {
            return Some(r.w.clone());
        }
        rows.retain(|r| r.coef.iter().any(|x| *x != 0));
        // eliminate the variable that creates the fewest new rows
        let mut best: Option<(usize, usize)> = None;
        for j in 0..natoms {
            let pos = rows.iter().filter(|r| r.coef[j] > 0).count();
            let neg = rows.iter().filter(|r| r.coef[j] < 0).count();
            if pos + neg == 0 {
                continue;
            }
            let cost = pos * neg;
            if best.is_none_or(|(_, b)| cost < b) {
                best = Some((j, cost));
            }
        }
        let (j, _) = best?;
        let (pos, rest): (Vec<Row>, Vec<Row>) = rows.into_iter().partition(|r| r.coef[j] > 0);
        let (neg, zero): (Vec<Row>, Vec<Row>) = rest.into_iter().partition(|r| r.coef[j] < 0);
        let mut next = zero;
        for p in &pos {
            for q in &neg {
                let (a, b) = (p.coef[j], -q.coef[j]);
                let comb = |x: &Vec<i128>, y: &Vec<i128>| -> Vec<i128> {
                    x.iter().zip(y).map(|(u, v)| u * b + v * a).collect()
                };
                next.push(Row {
                    coef: comb(&p.coef, &q.coef),
                    k: p.k * b + q.k * a,
                    w: comb(&p.w, &q.w),
                });
            }
        }
        if next.len() > 20_000 {
            return None;
        }
        // drop duplicates
        next.sort_by(|x, y| (&x.coef, x.k, &x.w).cmp(&(&y.coef, y.k, &y.w)));
        next.dedup_by(|x, y| x.coef == y.coef && x.k == y.k && x.w == y.w);
        rows = next;
    }
}

impl<'a> Cx<'a> {
    // ---- reification ----

    fn reify(&mut self, t: &T, atoms: &mut Vec<T>) -> Ex {
        let t = self.tc.zonk(t);
        if let Term::Lit(n) = &*t {
            return Ex::Const(*n);
        }
        let (h, args) = app_spine(&t);
        if let Term::Const(n, _) = &*h {
            match (&**n, args.len()) {
                ("Nat.zero", 0) => return Ex::Const(0),
                ("Nat.succ", 1) => {
                    let a = self.reify(&args[0], atoms);
                    return Ex::Add(Box::new(a), Box::new(Ex::Const(1)));
                }
                ("Nat.add", 2) => {
                    let a = self.reify(&args[0], atoms);
                    let b = self.reify(&args[1], atoms);
                    return Ex::Add(Box::new(a), Box::new(b));
                }
                ("Nat.mul", 2) => {
                    let a = self.reify(&args[0], atoms);
                    let b = self.reify(&args[1], atoms);
                    return match (a, b) {
                        (Ex::Const(x), Ex::Const(y)) => Ex::Const(x * y),
                        (Ex::Const(x), e) => Ex::Scale(x, Box::new(e)),
                        (e, Ex::Const(y)) => Ex::ScaleR(Box::new(e), y),
                        _ => self.atom(&t, atoms),
                    };
                }
                _ => {}
            }
        }
        self.atom(&t, atoms)
    }

    /// `v + c` or `c` for a `Nat` term made of one variable and literals; `None` otherwise.
    pub(super) fn nat_lin(&mut self, t: &T) -> Option<(Option<u32>, u64)> {
        let mut atoms = Vec::new();
        let e = self.reify(t, &mut atoms);
        fn go(e: &Ex, atoms: &[T]) -> Option<(Option<u32>, u64)> {
            match e {
                Ex::Const(n) => Some((None, *n)),
                Ex::Atom(i) => match &*atoms[*i] {
                    Term::FVar(v) => Some((Some(*v), 0)),
                    _ => None,
                },
                Ex::Add(a, b) => {
                    let (va, ca) = go(a, atoms)?;
                    let (vb, cb) = go(b, atoms)?;
                    match (va, vb) {
                        (Some(_), Some(_)) => None,
                        (v, None) | (None, v) => Some((v, ca + cb)),
                    }
                }
                _ => None,
            }
        }
        go(&e, &atoms)
    }

    fn atom(&mut self, t: &T, atoms: &mut Vec<T>) -> Ex {
        match atoms.iter().position(|a| a == t) {
            Some(i) => Ex::Atom(i),
            None => {
                atoms.push(t.clone());
                Ex::Atom(atoms.len() - 1)
            }
        }
    }

    /// Turn a hypothesis `proof : ty` into inequalities, if it is one.
    fn omega_facts(&mut self, proof: &T, ty: &T, atoms: &mut Vec<T>, out: &mut Vec<Fact>) {
        let ty = self.tc.zonk(ty);
        let (h, args) = app_spine(&ty);
        let Term::Const(n, ls) = &*h else { return };
        match (&**n, args.len()) {
            ("le", 2) => {
                let (lo, hi) = (self.reify(&args[0], atoms), self.reify(&args[1], atoms));
                out.push(Fact {
                    lo,
                    hi,
                    proof: proof.clone(),
                });
            }
            ("lt", 2) => {
                let lo = self.reify(&args[0], atoms);
                let hi = self.reify(&args[1], atoms);
                out.push(Fact {
                    lo: Ex::Add(Box::new(lo), Box::new(Ex::Const(1))),
                    hi,
                    proof: proof.clone(),
                });
            }
            ("Eq", 3) if matches!(&*args[0], Term::Const(m, _) if &**m == "Nat") => {
                let (a, b) = (args[1].clone(), args[2].clone());
                let (ea, eb) = (self.reify(&a, atoms), self.reify(&b, atoms));
                let p1 = mk_apps(&c("le_of_eq"), &[a.clone(), b.clone(), proof.clone()]);
                let sym = mk_apps(
                    &cnst("Eq.symm".into(), ls.clone()),
                    &[nat(), a.clone(), b.clone(), proof.clone()],
                );
                let p2 = mk_apps(&c("le_of_eq"), &[b, a, sym]);
                out.push(Fact {
                    lo: ea.clone(),
                    hi: eb.clone(),
                    proof: p1,
                });
                out.push(Fact {
                    lo: eb,
                    hi: ea,
                    proof: p2,
                });
            }
            ("And", 2) => {
                let l = mk_apps(
                    &c("And.left"),
                    &[args[0].clone(), args[1].clone(), proof.clone()],
                );
                let r = mk_apps(
                    &c("And.right"),
                    &[args[0].clone(), args[1].clone(), proof.clone()],
                );
                self.omega_facts(&l, &args[0], atoms, out);
                self.omega_facts(&r, &args[1], atoms, out);
            }
            ("Not", 1) => {
                let inner = self.tc.zonk(&args[0]);
                let (ih, iargs) = app_spine(&inner);
                if let (Term::Const(m, _), 2) = (&*ih, iargs.len()) {
                    match &**m {
                        "le" => {
                            // ¬ a ≤ b  gives  b < a
                            let p = mk_apps(
                                &c("lt_of_not_le"),
                                &[iargs[0].clone(), iargs[1].clone(), proof.clone()],
                            );
                            let lt = mk_apps(&c("lt"), &[iargs[1].clone(), iargs[0].clone()]);
                            self.omega_facts(&p, &lt, atoms, out);
                        }
                        "lt" => {
                            // ¬ a < b  gives  b ≤ a
                            let p = mk_apps(
                                &c("le_of_not_lt"),
                                &[iargs[1].clone(), iargs[0].clone(), proof.clone()],
                            );
                            let le = mk_apps(&c("le"), &[iargs[1].clone(), iargs[0].clone()]);
                            self.omega_facts(&p, &le, atoms, out);
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }

    fn omega_collect(&mut self, g: &Goal) -> (Vec<Fact>, Vec<T>) {
        let mut atoms = Vec::new();
        let mut facts = Vec::new();
        for (_, v) in &g.scope {
            if let Term::FVar(id) = &**v {
                if let Ok(ty) = self.tc.local_ty(*id) {
                    // instance calls (`a + b` as `Add.add Nat inst a b`) become `Nat.add a b`
                    let ty = self.tc.zonk(&ty);
                    let ty = self.devirt(&ty);
                    self.omega_facts(v, &ty, &mut atoms, &mut facts);
                }
            }
        }
        (facts, atoms)
    }

    // ---- goal manipulation ----

    pub(super) fn add_hyp(&mut self, st: &mut Tac, g: &Goal, name: &str, ty: T, proof: T) -> Goal {
        let fv = self.tc.fresh(name, ty.clone(), Mult::Omega);
        let mut ng = self.new_goal(g, g.target.clone(), "");
        ng.scope.push((name.to_string(), fvar(fv)));
        let lam_mv = self.tc.new_mvar(pi(Mult::Omega, ty, g.target.clone()));
        st.sol.insert(mvar_id(&lam_mv), Sol::Lam(vec![fv], ng.mv));
        self.solve(st, g, app(lam_mv, proof));
        ng
    }

    /// Reduce the goal to `False` with the negation as a hypothesis. May produce
    /// several goals (`a = b` needs both directions, `∧` both parts).
    fn omega_to_false(&mut self, st: &mut Tac, g: Goal, span: Span) -> R<Vec<Goal>> {
        let tgt = self.tc.zonk(&g.target);
        let (h, args) = app_spine(&tgt);
        let name = match &*h {
            Term::Const(n, _) => n.to_string(),
            _ => String::new(),
        };
        match (name.as_str(), args.len()) {
            ("False", 0) => Ok(vec![g]),
            ("le", 2) | ("lt", 2) => {
                // a ≤ b from ¬ b < a  (a < b is succ a ≤ b)
                let (a, b) = if name == "le" {
                    (args[0].clone(), args[1].clone())
                } else {
                    (app(c("Nat.succ"), args[0].clone()), args[1].clone())
                };
                let lt = mk_apps(&c("lt"), &[b.clone(), a.clone()]);
                let nt = app(c("Not"), lt);
                let ng = self.new_goal(&g, nt, "");
                self.solve(st, &g, mk_apps(&c("le_of_not_lt"), &[a, b, mvar(ng.mv)]));
                let mut gs = self.t_intro(
                    st,
                    ng,
                    &[Ident {
                        name: "neg".into(),
                        span,
                    }],
                    span,
                )?;
                let ng = gs.remove(0);
                self.omega_to_false(st, ng, span)
            }
            ("Eq", 3) if matches!(&*args[0], Term::Const(m, _) if &**m == "Nat") => {
                let (a, b) = (args[1].clone(), args[2].clone());
                let l1 = mk_apps(&c("le"), &[a.clone(), b.clone()]);
                let l2 = mk_apps(&c("le"), &[b.clone(), a.clone()]);
                let g1 = self.new_goal(&g, l1, "");
                let g2 = self.new_goal(&g, l2, "");
                self.solve(
                    st,
                    &g,
                    mk_apps(&c("le_antisymm"), &[a, b, mvar(g1.mv), mvar(g2.mv)]),
                );
                let mut out = self.omega_to_false(st, g1, span)?;
                out.extend(self.omega_to_false(st, g2, span)?);
                Ok(out)
            }
            ("And", 2) => {
                let g1 = self.new_goal(&g, args[0].clone(), "");
                let g2 = self.new_goal(&g, args[1].clone(), "");
                self.solve(
                    st,
                    &g,
                    mk_apps(
                        &c("And.intro"),
                        &[args[0].clone(), args[1].clone(), mvar(g1.mv), mvar(g2.mv)],
                    ),
                );
                let mut out = self.omega_to_false(st, g1, span)?;
                out.extend(self.omega_to_false(st, g2, span)?);
                Ok(out)
            }
            _ => {
                let w = from_kernel(self.tc.whnf(&tgt), span)?;
                if matches!(&*w, Term::Pi(..)) {
                    let mut gs = self.t_intro(
                        st,
                        g,
                        &[Ident {
                            name: "neg".into(),
                            span,
                        }],
                        span,
                    )?;
                    let ng = gs.remove(0);
                    return self.omega_to_false(st, ng, span);
                }
                err(
                    span,
                    format!(
                        "`omega` cannot handle the goal `{}`; it proves `=`, `le`, `lt`, `And`, \
                         `Not` and `False` goals about natural numbers",
                        self.pp_prop(&tgt)
                    ),
                )
            }
        }
    }

    /// Case-split one disjunction, disequality or truncated subtraction, if any.
    fn omega_split(
        &mut self,
        st: &mut Tac,
        os: &mut OmegaState,
        g: &Goal,
        span: Span,
    ) -> R<Option<Vec<Goal>>> {
        let scope = g.scope.clone();
        for (name, v) in &scope {
            let Term::FVar(id) = &**v else { continue };
            if os.done_hyps.contains(id) {
                continue;
            }
            let Ok(ty) = self.tc.local_ty(*id) else {
                continue;
            };
            let ty = self.tc.zonk(&ty);
            let (h, args) = app_spine(&ty);
            let Term::Const(n, _) = &*h else { continue };
            match (&**n, args.len()) {
                ("Or", 2) => {
                    os.done_hyps.insert(*id);
                    let x = Ident {
                        name: plain_name(name).to_string(),
                        span,
                    };
                    return Ok(Some(self.t_induct(
                        st,
                        g.clone(),
                        &x,
                        &[],
                        None,
                        false,
                        span,
                    )?));
                }
                ("Eq", 3) if matches!(&*args[0], Term::Const(m, _) if &**m == "Bool") => {
                    // `nat_lt a b = true/false`, `nat_beq a b = true/false`: what `<` and `==`
                    // conditions of an `if` give
                    let lhs = self.tc.zonk(&args[1]);
                    let (lh, largs) = app_spine(&lhs);
                    let truth = match &*args[2] {
                        Term::Const(m, _) if &**m == "Bool.true" => Some(true),
                        Term::Const(m, _) if &**m == "Bool.false" => Some(false),
                        _ => None,
                    };
                    if let (Term::Const(f, _), 2, Some(truth)) = (&*lh, largs.len(), truth) {
                        let (a, b) = (largs[0].clone(), largs[1].clone());
                        let derived = match (&**f, truth) {
                            ("nat_lt", true) => Some((
                                mk_apps(&c("lt"), &[a.clone(), b.clone()]),
                                mk_apps(&c("lt_sound"), &[a, b, v.clone()]),
                            )),
                            ("nat_lt", false) => Some((
                                mk_apps(&c("le"), &[b.clone(), a.clone()]),
                                mk_apps(&c("lt_false_le"), &[a, b, v.clone()]),
                            )),
                            ("nat_beq", true) => Some((
                                mk_apps(
                                    &cnst("Eq".into(), vec![Level::of_nat(1)]),
                                    &[nat(), a.clone(), b.clone()],
                                ),
                                mk_apps(&c("beq_sound"), &[a, b, v.clone()]),
                            )),
                            ("nat_beq", false) => Some((
                                app(
                                    c("Not"),
                                    mk_apps(
                                        &cnst("Eq".into(), vec![Level::of_nat(1)]),
                                        &[nat(), a.clone(), b.clone()],
                                    ),
                                ),
                                mk_apps(&c("beq_false_ne"), &[a, b, v.clone()]),
                            )),
                            _ => None,
                        };
                        if let Some((prop, pf)) = derived {
                            os.done_hyps.insert(*id);
                            return Ok(Some(vec![self.add_hyp(st, g, "cond", prop, pf)]));
                        }
                    }
                }
                ("Not", 1) => {
                    let inner = self.tc.zonk(&args[0]);
                    let (ih, iargs) = app_spine(&inner);
                    let is_nat_eq = matches!(&*ih, Term::Const(m, _) if &**m == "Eq")
                        && iargs.len() == 3
                        && matches!(&*iargs[0], Term::Const(m, _) if &**m == "Nat");
                    if is_nat_eq {
                        os.done_hyps.insert(*id);
                        let (a, b) = (iargs[1].clone(), iargs[2].clone());
                        let split_ty = mk_apps(
                            &c("Or"),
                            &[
                                mk_apps(&c("lt"), &[a.clone(), b.clone()]),
                                mk_apps(&c("lt"), &[b.clone(), a.clone()]),
                            ],
                        );
                        let pf = mk_apps(&c("ne_split"), &[a, b, v.clone()]);
                        let ng = self.add_hyp(st, g, "ne", split_ty, pf);
                        let x = Ident {
                            name: "ne".into(),
                            span,
                        };
                        return Ok(Some(self.t_induct(st, ng, &x, &[], None, false, span)?));
                    }
                }
                _ => {}
            }
        }
        // truncated subtraction: `a - b` is `0` when `a ≤ b`, and `a - b + b = a` otherwise
        let (_, atoms) = self.omega_collect(g);
        for a in atoms {
            let (h, args) = app_spine(&a);
            let is_sub = matches!(&*h, Term::Const(m, _) if &**m == "nat_sub") && args.len() == 2;
            if is_sub && !os.done_subs.contains(&a) {
                os.done_subs.push(a.clone());
                let (x, y) = (args[0].clone(), args[1].clone());
                let case_ty = {
                    let sub = a.clone();
                    let zero_eq = mk_apps(
                        &cnst("Eq".into(), vec![Level::of_nat(1)]),
                        &[nat(), sub.clone(), lit(0)],
                    );
                    let sum_eq = mk_apps(
                        &cnst("Eq".into(), vec![Level::of_nat(1)]),
                        &[nat(), mk_apps(&c("Nat.add"), &[sub, y.clone()]), x.clone()],
                    );
                    mk_apps(
                        &c("Or"),
                        &[
                            mk_apps(
                                &c("And"),
                                &[mk_apps(&c("le"), &[x.clone(), y.clone()]), zero_eq],
                            ),
                            mk_apps(
                                &c("And"),
                                &[mk_apps(&c("lt"), &[y.clone(), x.clone()]), sum_eq],
                            ),
                        ],
                    )
                };
                let pf = mk_apps(&c("sub_cases"), &[x, y]);
                let ng = self.add_hyp(st, g, "sub", case_ty, pf);
                let id = Ident {
                    name: "sub".into(),
                    span,
                };
                let parts = self.t_induct(st, ng, &id, &[], None, false, span)?;
                // each case holds an `And` of facts; the library facts are read from it
                return Ok(Some(parts));
            }
        }
        Ok(None)
    }

    fn omega_core(&mut self, st: &mut Tac, g: Goal, span: Span) -> R<()> {
        self.tc.zonk_locals();
        let (facts, atoms) = self.omega_collect(&g);
        let natoms = atoms.len();
        let Some(ws) = farkas(&facts, natoms) else {
            let mut lines = Vec::new();
            for (_, v) in &g.scope {
                if let Term::FVar(id) = &**v {
                    if let Ok(ty) = self.tc.local_ty(*id) {
                        let ty = self.tc.zonk(&ty);
                        let (h, _) = app_spine(&ty);
                        if matches!(&*h, Term::Const(m, _) if matches!(&**m, "le" | "lt" | "Eq" | "Not" | "And"))
                        {
                            lines.push(format!("  {}", self.pp_prop(&ty)));
                        }
                    }
                }
            }
            return err(
                span,
                format!(
                    "`omega` could not find a contradiction among the facts:\n{}",
                    lines.join("\n")
                ),
            );
        };
        // only the facts that take part in the certificate
        let used: Vec<(usize, u64)> = ws
            .iter()
            .enumerate()
            .filter(|(_, w)| **w > 0)
            .map(|(i, w)| (i, *w as u64))
            .collect();
        let cstr_ty = c("Cstr");
        let nat_ty = nat();
        let cs: Vec<T> = used
            .iter()
            .map(|(i, _)| {
                mk_apps(
                    &c("Cstr.mk"),
                    &[ex_term(&facts[*i].lo), ex_term(&facts[*i].hi)],
                )
            })
            .collect();
        let ws_t: Vec<T> = used.iter().map(|(_, w)| lit(*w)).collect();
        let cs_list = list_of(&cstr_ty, &cs);
        let ws_list = list_of(&nat_ty, &ws_t);
        let env_list = list_of(&nat_ty, &atoms);
        // holds cs env, one conjunct per used fact
        let mut holds_pf = c("True.intro");
        for k in (0..used.len()).rev() {
            let f = &facts[used[k].0];
            let le_prop = mk_apps(
                &c("le"),
                &[
                    mk_apps(&c("leval"), &[ex_term(&f.lo), env_list.clone()]),
                    mk_apps(&c("leval"), &[ex_term(&f.hi), env_list.clone()]),
                ],
            );
            let rest_list = list_of(&cstr_ty, &cs[k + 1..]);
            let rest_prop = mk_apps(&c("holds"), &[rest_list, env_list.clone()]);
            holds_pf = mk_apps(
                &c("And.intro"),
                &[le_prop, rest_prop, f.proof.clone(), holds_pf],
            );
        }
        let refl = mk_apps(
            &cnst("Eq.refl".into(), vec![Level::of_nat(1)]),
            &[c("Bool"), c("Bool.true")],
        );
        let pf = mk_apps(
            &c("omega_sound"),
            &[cs_list, ws_list, env_list, refl.clone(), refl, holds_pf],
        );
        if let Err(e) = self.tc.infer(&pf) {
            return err(
                span,
                format!(
                    "internal error: `omega` built an ill-typed certificate: {}",
                    e.0
                ),
            );
        }
        self.solve(st, &g, pf);
        Ok(())
    }

    pub(super) fn t_omega(&mut self, st: &mut Tac, g: Goal, span: Span) -> R<Vec<Goal>> {
        if self.env.get("omega_sound").is_none() {
            return err(span, "the `omega` library is not loaded");
        }
        // integer goals and hypotheses become statements about naturals first
        let g = self.int_to_nat(st, g, span)?;
        // each case split carries the splits already done on its path
        let mut work: Vec<(Goal, OmegaState)> = vec![(g, OmegaState::default())];
        let mut steps = 0;
        while let Some((cur, os)) = work.pop() {
            steps += 1;
            if steps > 400 {
                return err(span, "`omega` gave up: too many case splits");
            }
            let goals = self.omega_to_false(st, cur, span)?;
            for ng in goals.into_iter().rev() {
                let mut os = os.clone();
                match self.omega_split(st, &mut os, &ng, span)? {
                    Some(parts) => work.extend(parts.into_iter().rev().map(|p| (p, os.clone()))),
                    None => self.omega_core(st, ng, span)?,
                }
            }
        }
        Ok(vec![])
    }
}
