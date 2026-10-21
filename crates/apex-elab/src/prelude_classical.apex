// Classical logic: excluded middle derived from `Classical.choice`, `propext` and `funext`
// (Diaconescu's argument), so the only axioms used are the three Lean has.

struct Chosen<P: Prop -> Prop> { val: Prop, prop: P(val) }

fn choose(P: Prop -> Prop, h: Exists(P)) -> Chosen<P> {
    Classical.choice(match h { Exists.intro(w, hw) => Nonempty.intro(Chosen.mk(w, hw)) })
}
fn em_u(p: Prop) -> (Prop -> Prop) { |x: Prop| Or(x = True, p) }
fn em_v(p: Prop) -> (Prop -> Prop) { |x: Prop| Or(x = False, p) }

theorem em_uv(p: Prop, hp: p): em_u(p) = em_v(p) := funext(|x: Prop|
    propext(
        |h: Or(x = True, p)| Or.inr(hp),
        |h: Or(x = False, p)| Or.inr(hp)))

theorem choose_congr(P: Prop -> Prop, Q: Prop -> Prop, hP: Exists(P), hQ: Exists(Q), e: P = Q):
        Chosen.val(choose(P, hP)) = Chosen.val(choose(Q, hQ)) := by {
    cases e;
    rfl
}

theorem em(p: Prop): Or<p, Not<p>> := by {
    have hu: Exists(em_u(p)) := Exists.intro(True, Or.inl(rfl));
    have hv: Exists(em_v(p)) := Exists.intro(False, Or.inl(rfl));
    have su: Or<Chosen.val(choose(em_u(p), hu)) = True, p> := Chosen.prop(choose(em_u(p), hu));
    have sv: Or<Chosen.val(choose(em_v(p), hv)) = False, p> := Chosen.prop(choose(em_v(p), hv));
    cases su with {
        inr(hp) => { left; exact hp },
        inl(h1) => {
            cases sv with {
                inr(hp) => { left; exact hp },
                inl(h2) => {
                    right;
                    intro hp;
                    have c: Chosen.val(choose(em_u(p), hu)) = Chosen.val(choose(em_v(p), hv)) :=
                        choose_congr(em_u(p), em_v(p), hu, hv, em_uv(p, hp));
                    have tf: True = False := Eq.trans(Eq.symm(h1), Eq.trans(c, h2));
                    exact Eq.subst(|X: Prop| X, tf, True.intro)
                }
            }
        }
    }
}

theorem by_contradiction(p: Prop, h: Not<p> -> False): p := by {
    cases em(p) with {
        inl(hp) => { exact hp },
        inr(hn) => { exact False.elim(h(hn)) },
    }
}
theorem not_not(p: Prop, h: Not<Not<p>>): p := by_contradiction(p, h)
theorem or_not_of_imp(p: Prop, q: Prop, h: p -> q): Or<Not<p>, q> := by {
    cases em(p) with {
        inl(hp) => { right; exact h(hp) },
        inr(hn) => { left; exact hn },
    }
}
