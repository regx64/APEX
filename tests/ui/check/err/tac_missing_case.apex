// expect: missing case
theorem t(n: Nat): n = n := by { induction n with { zero => { rfl } } }
