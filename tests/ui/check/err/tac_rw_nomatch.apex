// expect: did not find an instance
theorem t(a: Nat, b: Nat, h: a = b): 5 = 5 := by { rw [h] }
