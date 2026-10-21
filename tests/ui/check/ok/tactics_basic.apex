theorem t_refl(n: Nat): n = n := by { rfl }
theorem t_exact(n: Nat): n = n := by { exact rfl }
theorem t_intro<P: Prop, Q: Prop>(): P -> Q -> P := by { intro p q; exact p }
theorem t_assump<P: Prop, Q: Prop>(p: P, q: Q): P := by { assumption }
theorem t_and<P: Prop, Q: Prop>(p: P, q: Q): And<P, Q> := by { constructor; exact p; exact q }
theorem t_apply<P: Prop, Q: Prop>(f: P -> Q, p: P): Q := by { apply f; exact p }
theorem t_or<P: Prop, Q: Prop>(q: Q): Or<P, Q> := by { right; exact q }
theorem t_symm(a: Nat, b: Nat, h: a = b): b = a := by { symm; exact h }
theorem t_have<P: Prop>(p: P): P := by { have h: P := p; exact h }
theorem t_decide(): 2 + 3 = 5 := by { decide }
theorem t_rw(a: Nat, b: Nat, h: a = b): Nat.succ(a) = Nat.succ(b) := by { rw [h] }
theorem t_cases_and<P: Prop, Q: Prop>(h: And<P, Q>): And<Q, P> := by {
    cases h with { intro(p, q) => { constructor; exact q; exact p } }
}
theorem t_cases_or<P: Prop, Q: Prop>(h: Or<P, Q>): Or<Q, P> := by {
    cases h with {
        inl(p) => { right; exact p },
        inr(q) => { left; exact q },
    }
}
theorem t_exfalso<P: Prop>(h: False): P := by { exfalso; exact h }
theorem t_contra<P: Prop>(h: False): P := by { contradiction }
