// expect: depends on
theorem t(n: Nat, h: n = n): n = n := by { induction n with { zero => { rfl }, succ(m, ih) => { rfl } } }
