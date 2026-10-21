// expect: `calc` proves
theorem bad3(a: Nat, b: Nat, h: a <= b): lt(a, b) := by { calc { a <= b := h } }
