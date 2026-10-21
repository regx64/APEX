fn double(a: Int) -> Int { a * 2 + 1 }
theorem d3(): double(3) = 7 := by { rfl }
theorem neg5(): (-5 : Int) + 3 = -2 := by { rfl }
theorem mixed(): (3 : Int) - 5 = -2 := by { rfl }
theorem comm(a: Int, b: Int): a + b = b + a := int_add_comm(a, b)
theorem distrib(a: Int, b: Int, c: Int): a * (b + c) = a * b + a * c := int_mul_add(a, b, c)
theorem neg_cancel(a: Int): a + -a = 0 := int_add_neg_cancel(a)
theorem le_ref(a: Int): int_le(a, a) := int_le_refl(a)
theorem le_op(a: Int): a <= a := int_le_refl(a)
