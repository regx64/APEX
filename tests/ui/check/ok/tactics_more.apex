theorem g1(n: Nat, m: Nat): n + m = m + n := by {
    induction n generalizing m with {
        zero => { simp },
        succ(k, ih) => { simp [ih] },
    }
}
// a hypothesis that depends on the variable is reverted automatically
theorem g2(n: Nat, h: n = n): n + 0 = n := by {
    induction n with {
        zero => { rfl },
        succ(k, ih) => { rfl },
    }
}
theorem g3(a: Nat, b: Nat, c: Nat, h: a = b, g: a = c): b = c := by { rw [h] at g; exact g }
theorem g4(a: Nat, b: Nat, h: a = b, g: b = 3): a = 3 := by { rw [g] at h; exact h }
theorem g5(a: Nat): Exists(|k: Nat| a + k = a + 2) := by { exists 2 }
theorem g6(a: Nat, b: Nat): a = b -> b = a := by { revert a; intro a h; symm; exact h }
