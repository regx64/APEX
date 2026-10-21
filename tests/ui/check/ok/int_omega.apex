theorem o1(a: Int, b: Int, h: a = b): b = a := by { omega }
theorem o2(a: Int, b: Int): a + b - b = a := by { omega }
theorem o3(a: Int, b: Int, h: int_le(a, b)): int_le(a - 1, b) := by { omega }
theorem o4(a: Int, b: Int, h1: int_lt(a, b), h2: int_lt(b, a)): False := by { omega }
theorem o5(a: Int): int_le(a, a + 1) := by { omega }
theorem o6(a: Int, b: Int, h: a <= b): -b <= -a := by { omega }
theorem o7(x: Int, y: Int, h1: x + y = 10, h2: x - y = 2): x = 6 := by { omega }
theorem o8(a: Int, b: Int, h: a != b): Not<a = b> := by { omega }
theorem r1(a: Int, b: Int): (a + b) * (a + b) = a * a + 2 * a * b + b * b := by { ring }
theorem r2(a: Int, b: Int): (a - b) * (a + b) = a * a - b * b := by { ring }
theorem r3(a: Int): a * 0 + -a + a = 0 := by { ring }
