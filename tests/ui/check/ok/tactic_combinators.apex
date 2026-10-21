// tactic combinators and user-defined tactics
tactic finish { first | rfl | assumption | omega }
tactic with_lemma(l) { rw [l]; try rfl }

theorem t1<P: Prop, Q: Prop>(p: P, q: Q): And<P, Q> := by { constructor <;> assumption }
theorem t2(a: Nat, b: Nat, h: lt(a, b)): le(a, b) := by { first | rfl | omega }
theorem t3<P: Prop>(p: P): And<P, And<P, P>> := by {
    repeat constructor;
    all_goals assumption
}
theorem t4(n: Nat): n + 0 = n := by { try omega }
theorem t5(n: Nat, m: Nat, h: n = m): Nat.succ(n) = Nat.succ(m) := by { with_lemma(h) }
theorem t6(a: Nat, b: Nat, h: le(a, b)): le(a, b + 1) := by { finish }
theorem t7<P: Prop, Q: Prop>(p: P, q: Q): And<Q, P> := by {
    constructor;
    any_goals assumption
}
theorem t8(n: Nat): n = n := by { skip; rfl }
