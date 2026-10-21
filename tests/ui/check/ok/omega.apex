theorem o1(x: Nat, h: le(x + 1, x)): False := by { omega }
theorem o2(x: Nat, y: Nat, h: le(x, y)): le(x, y + 1) := by { omega }
theorem o3(x: Nat, y: Nat, h: lt(x, y)): lt(x, y + 1) := by { omega }
theorem o4(x: Nat): lt(x, x + 1) := by { omega }
theorem o5(x: Nat, y: Nat, h1: le(x, y), h2: le(y, x)): x = y := by { omega }
theorem o6(x: Nat, y: Nat, z: Nat, h1: le(x, y), h2: le(y, z)): le(x, z) := by { omega }
theorem o7(x: Nat, y: Nat): le(2 * x + 3 * y, 2 * (x + y) + y) := by { omega }
theorem o8(x: Nat): le(x * 2, x + x) := by { omega }
theorem o9(n: Nat, h: lt(0, n)): lt(nat_sub(n, 1), n) := by { omega }
theorem o10(a: Nat, b: Nat, h: Or<le(a, 3), le(b, 3)>): le(a + b, a + 3 + b) := by { omega }
theorem o12(a: Nat, b: Nat, h: Not<a = b>): lt(0, nat_sub(a, b) + nat_sub(b, a)) := by { omega }
theorem o13(a: Nat, b: Nat, c: Nat, h1: lt(a, b), h2: lt(b, c)): lt(a + 1, c) := by { omega }
theorem o14(x: Nat, y: Nat, h: x + y = 10, g: x = 3): y = 7 := by { omega }
theorem o15(n: Nat, h: Not<n = 0>): le(1, n) := by { omega }
theorem o16(n: Nat, m: Nat): le(nat_sub(n, m), n) := by { omega }
theorem o17(n: Nat, h: Not<lt(n, 5)>): le(5, n + 0) := by { omega }
