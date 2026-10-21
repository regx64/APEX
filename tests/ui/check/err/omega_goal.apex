// expect: cannot handle the goal
theorem bad(x: Nat): Or<le(x, 1), le(2, x)> := by { omega }
