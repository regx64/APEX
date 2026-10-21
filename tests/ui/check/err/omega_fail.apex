// expect: could not find a contradiction
theorem bad(x: Nat, y: Nat, h: le(x, y)): le(y, x) := by { omega }
