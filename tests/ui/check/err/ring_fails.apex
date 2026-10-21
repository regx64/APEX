// expect: different normal forms
theorem bad(x: Nat, y: Nat): (x + y) * (x + y) = x * x + y * y := by { ring }
