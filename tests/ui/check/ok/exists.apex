fn le(a: Nat, b: Nat) -> Prop { Exists(|k: Nat| a + k = b) }
theorem le_refl(a: Nat): le(a, a) := Exists.intro(0, rfl)
theorem le_succ(a: Nat): le(a, Nat.succ(a)) := Exists.intro(1, rfl)
