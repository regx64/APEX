theorem zero_add_(n: Nat): 0 + n = n := by {
    induction n with {
        zero => { rfl },
        succ(m, ih) => { exact congr_arg(Nat.succ, ih) },
    }
}
theorem succ_add_(n: Nat, m: Nat): Nat.succ(n) + m = Nat.succ(n + m) := by {
    induction m with {
        zero => { rfl },
        succ(k, ih) => { exact congr_arg(Nat.succ, ih) },
    }
}
theorem add_comm_(a: Nat, b: Nat): a + b = b + a := by {
    induction b with {
        zero => { symm; exact zero_add_(a) },
        succ(k, ih) => {
            show Nat.succ(a + k) = Nat.succ(k) + a;
            rw [succ_add_, ih]
        },
    }
}
theorem flat(n: Nat): n + 0 = n := by {
    induction n
    { rfl }
    { rfl }
}
