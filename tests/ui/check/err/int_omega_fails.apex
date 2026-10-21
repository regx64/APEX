// expect: `omega` could not find a contradiction
theorem bad(a: Int, b: Int): a + b = a := by { omega }
