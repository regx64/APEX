// the SPEC example, in the structured form
theorem add_comm2(a: Nat, b: Nat): a + b = b + a := by {
    induction a with {
        zero => { simp },
        succ(n, ih) => { simp [ih] },
    }
}
theorem s1(n: Nat): n + 0 = n := by { simp }
theorem s2(n: Nat, m: Nat): Nat.succ(n) + m = Nat.succ(m + n) := by { simp [add_comm] }
theorem s3(a: Nat, b: Nat, c: Nat): (a + b) + c = a + (c + b) := by { rw [add_assoc, add_comm(b, c)] }
theorem s4(n: Nat): 2 * (n + 0) = n + n := by { simp }
theorem s5(): 2 * 3 = 6 := by { decide }
fn double(n: Nat) -> Nat { n + n }
theorem s6(n: Nat): double(n) = n + n := by { unfold double }
theorem s7(n: Nat): double(n) = n + n := by { simp [double] }
theorem s8(n: Nat): double(n) = 2 * n := by { unfold double; simp [add_comm, mul_succ]; }
