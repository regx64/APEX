// omega
// conditional rewriting: the side condition `lt(0, n)` comes from the context
theorem pred_succ_lemma(n: Nat, h: lt(0, n)): nat_sub(n, 1) + 1 = n := by { omega }
theorem cond(n: Nat, h: lt(0, n)): (nat_sub(n, 1) + 1) + 0 = n := by { simp [pred_succ_lemma] }

// the side condition is found by omega
theorem cond_omega(n: Nat, k: Nat, h: lt(k, n)): nat_sub(n, 1) + 1 = n := by { simp [pred_succ_lemma] }

// simp only uses nothing but the given rules
theorem only_rule(a: Nat, b: Nat, h: a = b): a + 0 = b := by { simp only [h] }
theorem only_no_lib(n: Nat): 0 + n = n := by { simp only [zero_add] }

// simp_arith: simp, then omega
theorem arith(a: Nat, b: Nat, h: le(a, b)): le(a + 0, b + 1) := by { simp_arith }
theorem arith2(n: Nat): lt(n * 1, n + 1) := by { simp_arith }

// simp_all: equations among the hypotheses are rules
theorem all(a: Nat, b: Nat, c: Nat, h1: a = b, h2: b = c): a + 0 = c := by { simp_all }
