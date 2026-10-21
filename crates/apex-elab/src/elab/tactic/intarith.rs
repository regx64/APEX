//! `omega` and `ring` for `Int`: translate an integer statement into a `Nat` one.
//!
//! Every integer `z` has a representation `int_rep z p q` (`z = p - q` for naturals), and the
//! operations act on pairs (`int_add_rep`, `int_neg_rep`, `int_mul_rep`, library
//! `prelude_int.apex`). Each integer atom is replaced by a fresh pair `(p, q)`; an integer
//! expression becomes a pair of `Nat` expressions together with a proof of `int_rep`, and a
//! relation between integers becomes a relation between those `Nat` expressions
//! (`a = b` iff `P_a + Q_b = P_b + Q_a`, `a ≤ b` iff `P_a + Q_b ≤ P_b + Q_a`). The result is
//! an ordinary `Nat` goal for `omega` or `ring`; all the reasoning is in the verified library.

use super::*;

#[derive(Clone)]
enum IntRel {
    Eq(T, T),
    Le(T, T),
    Lt(T, T),
    Not(Box<IntRel>),
}

struct IntAtom {
    term: T,
    p: T,
    q: T,
    h: T,
}

enum IntView {
    Add(T, T),
    Sub(T, T),
    Mul(T, T),
    Neg(T),
    OfNat(T),
    NegSucc(T),
    Atom,
}

fn nat_add(a: T, b: T) -> T {
    mk_apps(&cnst("Nat.add".into(), vec![]), &[a, b])
}

fn nat_mul(a: T, b: T) -> T {
    mk_apps(&cnst("Nat.mul".into(), vec![]), &[a, b])
}

fn lib(name: &str, args: &[T]) -> T {
    mk_apps(&cnst(name.into(), vec![]), args)
}

impl<'a> Cx<'a> {
    fn int_const() -> T {
        cnst("Int".into(), vec![])
    }

    fn int_view(&mut self, e: &T) -> IntView {
        let (h, args) = app_spine(e);
        let Term::Const(n, _) = &*h else {
            return IntView::Atom;
        };
        match (&**n, args.len()) {
            ("int_add", 2) => IntView::Add(args[0].clone(), args[1].clone()),
            ("int_sub", 2) => IntView::Sub(args[0].clone(), args[1].clone()),
            ("int_mul", 2) => IntView::Mul(args[0].clone(), args[1].clone()),
            ("int_neg", 1) => IntView::Neg(args[0].clone()),
            ("Int.ofNat", 1) => IntView::OfNat(args[0].clone()),
            ("Int.negSucc", 1) => IntView::NegSucc(args[0].clone()),
            _ => IntView::Atom,
        }
    }

    /// `Eq Int a b`, `int_le a b`, `int_lt a b`, or a negation of one.
    fn int_rel(&mut self, ty: &T) -> Option<IntRel> {
        let ty = self.tc.zonk(ty);
        let (h, args) = app_spine(&ty);
        match &*h {
            Term::Const(n, _) => match (&**n, args.len()) {
                ("Eq", 3) if matches!(&*args[0], Term::Const(i, _) if &**i == "Int") => {
                    Some(IntRel::Eq(args[1].clone(), args[2].clone()))
                }
                ("int_le", 2) => Some(IntRel::Le(args[0].clone(), args[1].clone())),
                ("int_lt", 2) => Some(IntRel::Lt(args[0].clone(), args[1].clone())),
                ("Not", 1) => self.int_rel(&args[0]).map(|r| IntRel::Not(Box::new(r))),
                ("ne", 3) if matches!(&*args[0], Term::Const(i, _) if &**i == "Int") => Some(
                    IntRel::Not(Box::new(IntRel::Eq(args[1].clone(), args[2].clone()))),
                ),
                _ => None,
            },
            Term::Pi(_, p, q)
                if matches!(&**q, Term::Const(f, _) if &**f == "False") && !has_bvar(p) =>
            {
                self.int_rel(p).map(|r| IntRel::Not(Box::new(r)))
            }
            _ => None,
        }
    }

    fn rel_sides(r: &IntRel) -> (&T, &T) {
        match r {
            IntRel::Eq(a, b) | IntRel::Le(a, b) | IntRel::Lt(a, b) => (a, b),
            IntRel::Not(r) => Self::rel_sides(r),
        }
    }

    fn collect_int_atoms(&mut self, e: &T, out: &mut Vec<T>) {
        let e = self.tc.zonk(e);
        match self.int_view(&e) {
            IntView::Add(a, b) | IntView::Sub(a, b) | IntView::Mul(a, b) => {
                self.collect_int_atoms(&a, out);
                self.collect_int_atoms(&b, out);
            }
            IntView::Neg(a) => self.collect_int_atoms(&a, out),
            IntView::OfNat(_) | IntView::NegSucc(_) => {}
            IntView::Atom => {
                if !out.contains(&e) {
                    out.push(e);
                }
            }
        }
    }

    /// `(P, Q, proof of int_rep e P Q)`
    fn int_pair(&mut self, e: &T, atoms: &[IntAtom], span: Span) -> R<(T, T, T)> {
        let e = self.tc.zonk(e);
        let zero = lit(0);
        Ok(match self.int_view(&e) {
            IntView::Add(a, b) => {
                let (pa, qa, ha) = self.int_pair(&a, atoms, span)?;
                let (pb, qb, hb) = self.int_pair(&b, atoms, span)?;
                let pf = lib(
                    "int_add_rep",
                    &[a, b, pa.clone(), qa.clone(), pb.clone(), qb.clone(), ha, hb],
                );
                (nat_add(pa, pb), nat_add(qa, qb), pf)
            }
            IntView::Sub(a, b) => {
                // a - b is a + (-b)
                let (pa, qa, ha) = self.int_pair(&a, atoms, span)?;
                let (pb, qb, hb) = self.int_pair(&b, atoms, span)?;
                let nb = lib("int_neg", std::slice::from_ref(&b));
                let hnb = lib("int_neg_rep", &[b, pb.clone(), qb.clone(), hb]);
                let pf = lib(
                    "int_add_rep",
                    &[
                        a,
                        nb,
                        pa.clone(),
                        qa.clone(),
                        qb.clone(),
                        pb.clone(),
                        ha,
                        hnb,
                    ],
                );
                (nat_add(pa, qb), nat_add(qa, pb), pf)
            }
            IntView::Mul(a, b) => {
                let (pa, qa, ha) = self.int_pair(&a, atoms, span)?;
                let (pb, qb, hb) = self.int_pair(&b, atoms, span)?;
                let pf = lib(
                    "int_mul_rep",
                    &[a, b, pa.clone(), qa.clone(), pb.clone(), qb.clone(), ha, hb],
                );
                (
                    nat_add(
                        nat_mul(pa.clone(), pb.clone()),
                        nat_mul(qa.clone(), qb.clone()),
                    ),
                    nat_add(nat_mul(pa, qb), nat_mul(qa, pb)),
                    pf,
                )
            }
            IntView::Neg(a) => {
                let (pa, qa, ha) = self.int_pair(&a, atoms, span)?;
                let pf = lib("int_neg_rep", &[a, pa.clone(), qa.clone(), ha]);
                (qa, pa, pf)
            }
            IntView::OfNat(n) => (n.clone(), zero, lib("int_ofNat_rep", &[n])),
            IntView::NegSucc(n) => (
                zero,
                app(cnst("Nat.succ".into(), vec![]), n.clone()),
                lib("int_negSucc_rep", &[n]),
            ),
            IntView::Atom => match atoms.iter().find(|a| a.term == e) {
                Some(a) => (a.p.clone(), a.q.clone(), a.h.clone()),
                None => {
                    return err(
                        span,
                        "internal error: an integer atom has no representation",
                    )
                }
            },
        })
    }

    /// Prepare an integer goal for the `Nat` tactics: `Some(goal)` is a `Nat` goal (with
    /// the integer hypotheses translated into `Nat` facts) whose proof proves `g`.
    pub(super) fn int_to_nat(&mut self, st: &mut Tac, g: Goal, span: Span) -> R<Goal> {
        // (the library defines these lemmas last; while it is still being built there is nothing to do)
        if self.env.get("int_not_lt_cross").is_none() {
            return Ok(g);
        }
        // a negated goal: assume the relation and prove `False`
        let tgt = self.tc.zonk(&g.target);
        let mut g = g;
        if let Some(IntRel::Not(_)) = self.int_rel(&tgt) {
            let gs = self.t_intro(
                st,
                g,
                &[Ident {
                    name: "_neg".into(),
                    span,
                }],
                span,
            )?;
            g = gs.into_iter().next().expect("intro gives one goal");
        }
        let tgt = self.tc.zonk(&g.target);
        let goal_rel = self.int_rel(&tgt);
        // hypotheses about integers
        let mut hyps: Vec<(T, IntRel)> = Vec::new();
        for (_, v) in &g.scope {
            if let Term::FVar(id) = &**v {
                if let Ok(ty) = self.tc.local_ty(*id) {
                    if let Some(r) = self.int_rel(&ty) {
                        hyps.push((v.clone(), r));
                    }
                }
            }
        }
        if goal_rel.is_none() && hyps.is_empty() {
            return Ok(g);
        }
        if let Some(r) = &goal_rel {
            if matches!(r, IntRel::Not(_)) {
                return err(span, "internal error: a negated goal was not introduced");
            }
        }
        // atoms
        let mut atom_terms = Vec::new();
        let sides = |r: &IntRel| {
            let (a, b) = Self::rel_sides(r);
            (a.clone(), b.clone())
        };
        let all_rels: Vec<IntRel> = goal_rel
            .iter()
            .cloned()
            .chain(hyps.iter().map(|(_, r)| r.clone()))
            .collect();
        for r in &all_rels {
            let (a, b) = sides(r);
            self.collect_int_atoms(&a, &mut atom_terms);
            self.collect_int_atoms(&b, &mut atom_terms);
        }
        // a representation for each atom: `obtain (p, q, h) := int_exists_rep atom`
        let base = g.scope.len();
        let mut atoms: Vec<IntAtom> = Vec::new();
        for (k, at) in atom_terms.iter().enumerate() {
            let pf = lib("int_exists_rep", std::slice::from_ref(at));
            let ty = from_kernel(self.tc.infer(&pf), span)?;
            let ty = self.tc.zonk(&ty);
            let hn = format!("_iex{base}_{k}");
            let ng = self.add_hyp(st, &g, &hn, ty, pf);
            let pat = RPat::Tuple(vec![
                RPat::Name(format!("_ip{base}_{k}")),
                RPat::Name(format!("_iq{base}_{k}")),
                RPat::Name(format!("_ih{base}_{k}")),
            ]);
            let mut gs = self.rpat(st, ng, &hn, &pat, span)?;
            if gs.len() != 1 {
                return err(span, "internal error: destructuring a representation");
            }
            g = gs.remove(0);
            let find = |n: &str, g: &Goal| {
                g.scope
                    .iter()
                    .rfind(|(m, _)| m == n)
                    .map(|(_, v)| v.clone())
                    .expect("introduced above")
            };
            atoms.push(IntAtom {
                term: at.clone(),
                p: find(&format!("_ip{base}_{k}"), &g),
                q: find(&format!("_iq{base}_{k}"), &g),
                h: find(&format!("_ih{base}_{k}"), &g),
            });
        }
        // Nat facts from the hypotheses
        for (hv, r) in &hyps {
            let (a, b) = sides(r);
            let (pa, qa, ha) = self.int_pair(&a, &atoms, span)?;
            let (pb, qb, hb) = self.int_pair(&b, &atoms, span)?;
            let name = match r {
                IntRel::Eq(..) => "int_eq_cross",
                IntRel::Le(..) => "int_rep_of_le",
                IntRel::Lt(..) => "int_rep_of_lt",
                IntRel::Not(inner) => match &**inner {
                    IntRel::Eq(..) => "int_ne_cross",
                    IntRel::Le(..) => "int_not_le_cross",
                    IntRel::Lt(..) => "int_not_lt_cross",
                    IntRel::Not(_) => continue,
                },
            };
            let fact = lib(name, &[a, b, pa, qa, pb, qb, ha, hb, hv.clone()]);
            let ty = from_kernel(self.tc.infer(&fact), span)?;
            let ty = self.tc.zonk(&ty);
            let fname = format!("_inat{}", g.scope.len());
            g = self.add_hyp(st, &g, &fname, ty, fact);
        }
        // the goal itself
        match goal_rel {
            None => Ok(g),
            Some(rel) => {
                let (a, b) = sides(&rel);
                let (pa, qa, ha) = self.int_pair(&a, &atoms, span)?;
                let (pb, qb, hb) = self.int_pair(&b, &atoms, span)?;
                let lhs = nat_add(pa.clone(), qb.clone());
                let rhs = nat_add(pb.clone(), qa.clone());
                let (lemma, target) = match &rel {
                    IntRel::Eq(..) => (
                        "int_eq_by_cross",
                        mk_apps(
                            &cnst("Eq".into(), vec![Level::of_nat(1)]),
                            &[cnst("Nat".into(), vec![]), lhs, rhs],
                        ),
                    ),
                    IntRel::Le(..) => ("int_le_of_rep", lib("le", &[lhs, rhs])),
                    IntRel::Lt(..) => ("int_lt_of_rep", lib("lt", &[lhs, rhs])),
                    IntRel::Not(_) => unreachable!("introduced above"),
                };
                let ng = self.new_goal(&g, target, "");
                let pf = match &rel {
                    IntRel::Eq(..) => lib(lemma, &[a, b, pa, qa, pb, qb, ha, hb, mvar(ng.mv)]),
                    _ => lib(lemma, &[a, b, pa, qa, pb, qb, ha, hb, mvar(ng.mv)]),
                };
                self.solve(st, &g, pf);
                let _ = Self::int_const;
                Ok(ng)
            }
        }
    }
}
