//! `ring`: reify both sides of a `Nat` equation as `RE` expressions and apply the verified
//! `ring_sound` (library `prelude_ring.apex`); the kernel checks that the two normal forms
//! agree by computation.

use super::*;

impl<'a> Cx<'a> {
    fn ring_reify(&mut self, t: &T, atoms: &mut Vec<T>) -> T {
        let t = self.tc.zonk(t);
        let (h, args) = app_spine(&t);
        let re = |n: &str, a: Vec<T>| mk_apps(&cnst(n.into(), vec![]), &a);
        match &*h {
            Term::Const(n, _) if args.len() == 2 && &**n == "Nat.add" => {
                let (a, b) = (
                    self.ring_reify(&args[0], atoms),
                    self.ring_reify(&args[1], atoms),
                );
                return re("RE.RAdd", vec![a, b]);
            }
            Term::Const(n, _) if args.len() == 2 && &**n == "Nat.mul" => {
                let (a, b) = (
                    self.ring_reify(&args[0], atoms),
                    self.ring_reify(&args[1], atoms),
                );
                return re("RE.RMul", vec![a, b]);
            }
            Term::Const(n, _) if args.len() == 1 && &**n == "Nat.succ" => {
                let a = self.ring_reify(&args[0], atoms);
                return re("RE.RAdd", vec![a, re("RE.RConst", vec![lit(1)])]);
            }
            Term::Const(n, _) if args.is_empty() && &**n == "Nat.zero" => {
                return re("RE.RConst", vec![lit(0)]);
            }
            _ => {}
        }
        if let Term::Lit(_) = &*t {
            return re("RE.RConst", vec![t]);
        }
        let idx = match atoms.iter().position(|a| *a == t) {
            Some(i) => i,
            None => {
                atoms.push(t.clone());
                atoms.len() - 1
            }
        };
        re("RE.RVar", vec![lit(idx as u64)])
    }

    pub(super) fn t_ring(&mut self, st: &mut Tac, g: Goal, span: Span) -> R<Vec<Goal>> {
        if self.env.get("ring_sound").is_none() {
            return err(
                span,
                "`ring` needs its library (it is loaded when the program mentions `ring`)",
            );
        }
        let Some((_, alpha, a, b)) = self.eq_parts(&g.target) else {
            return err(span, "`ring` needs a goal `a = b`");
        };
        // an equation between integers: translate to the natural numbers first
        let int = cnst("Int".into(), vec![]);
        if self.env.get("int_not_lt_cross").is_some() && self.def_eq(&alpha, &int) {
            let ng = self.int_to_nat(st, g, span)?;
            return self.t_ring(st, ng, span);
        }
        let nat = cnst("Nat".into(), vec![]);
        if !self.def_eq(&alpha, &nat) {
            return err(span, "`ring` works on equations between natural numbers");
        }
        let mut atoms = Vec::new();
        let ra = self.ring_reify(&a, &mut atoms);
        let rb = self.ring_reify(&b, &mut atoms);
        let mut env = mk_apps(
            &cnst("List.nil".into(), vec![Level::zero()]),
            std::slice::from_ref(&nat),
        );
        for at in atoms.iter().rev() {
            env = mk_apps(
                &cnst("List.cons".into(), vec![Level::zero()]),
                &[nat.clone(), at.clone(), env],
            );
        }
        let norm = |r: &T| app(cnst("norm".into(), vec![]), r.clone());
        let (na, nb) = (norm(&ra), norm(&rb));
        if !self.def_eq(&na, &nb) {
            return err(
                span,
                format!(
                    "`ring` failed: the two sides have different normal forms\n  {}\n  {}",
                    self.pp(&a),
                    self.pp(&b)
                ),
            );
        }
        let refl = mk_apps(
            &cnst("Eq.refl".into(), vec![Level::of_nat(1)]),
            &[
                app(
                    cnst("List".into(), vec![Level::zero()]),
                    app(
                        app(cnst("Prod".into(), vec![]), nat.clone()),
                        app(cnst("List".into(), vec![Level::zero()]), nat),
                    ),
                ),
                na,
            ],
        );
        let pf = mk_apps(&cnst("ring_sound".into(), vec![]), &[env, ra, rb, refl]);
        if let Err(e) = self.tc.infer(&pf) {
            return err(span, format!("`ring` produced an ill-typed proof: {}", e.0));
        }
        self.solve(st, &g, pf);
        Ok(vec![])
    }
}
