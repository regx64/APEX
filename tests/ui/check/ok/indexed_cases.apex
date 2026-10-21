// cases and induction on indexed families: the indices must be variables
theorem eq_symm2<A: Type>(a: A, b: A, h: a = b): b = a := by {
    cases h with { refl => { rfl } }
}

theorem eq_trans2<A: Type>(a: A, b: A, c: A, h1: a = b, h2: b = c): a = c := by {
    cases h2 with { refl => { exact h1 } }
}

// the equation is used to rewrite hypotheses that mention the index
theorem eq_cong<A: Type, B: Type>(f: A -> B, a: A, b: A, h: a = b): f(a) = f(b) := by {
    cases h with { refl => { rfl } }
}

theorem eq_transport(a: Nat, b: Nat, h: a = b, g: lt(a, 5)): lt(b, 5) := by {
    cases h with { refl => { exact g } }
}
