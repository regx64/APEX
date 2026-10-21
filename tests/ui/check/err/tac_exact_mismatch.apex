// expect: does not match the expected
theorem t(n: Nat): n = n := by { exact Eq.refl(0) }
