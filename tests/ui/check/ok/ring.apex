theorem sq(x: Nat, y: Nat): (x + y) * (x + y) = x * x + 2 * (x * y) + y * y := by { ring }
theorem cube(a: Nat): (a + 1) * (a + 1) * (a + 1) = a * a * a + 3 * (a * a) + 3 * a + 1 := by { ring }
theorem comm3(a: Nat, b: Nat, c: Nat): a * b * c = c * (b * a) := by { ring }
theorem succ_form(n: Nat): Nat.succ(n) * 2 = 2 * n + 2 := by { ring }
theorem zero_form(x: Nat): x * 0 + 0 = 0 := by { ring }
theorem atoms(f: Nat -> Nat, x: Nat): f(x) * (f(x) + 1) = f(x) * f(x) + f(x) := by { ring }
theorem use_in_calc(a: Nat, b: Nat): (a + b) * (a + b) = a * a + 2 * a * b + b * b := by {
    calc {
        (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by { ring };
        _ = a * a + 2 * a * b + b * b := by { ring }
    }
}
