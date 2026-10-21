theorem c1(a: Nat, b: Nat, c: Nat, h: a = b): a + c = b + c := by {
    conv { lhs; arg 1; rw [h] }
}
theorem c2(a: Nat, b: Nat): a + b = b + a := by {
    conv { lhs; rw [add_comm] }
}
theorem c3(a: Nat, b: Nat, c: Nat): (a + b) * c = c * (b + a) := by {
    conv { lhs; arg 1; rw [add_comm] };
    rw [mul_comm]
}
theorem c4(a: Nat, b: Nat, h: a + 0 = b): b = a := by {
    conv at h { lhs; simp };
    symm; exact h
}
theorem c5(x: Nat): x + 0 + 0 = x := by {
    conv { lhs; arg 1; simp }
}
theorem c6(a: Nat, b: Nat, h: a = b): (a + 1) * 2 = (b + 1) * 2 := by {
    conv { rhs; arg 1; arg 1; rw [<- h] }
}
