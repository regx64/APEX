theorem a1(): 1000000 - 1 = 999999 := by { rfl }
theorem a2(): 100000000 / 7 = 14285714 := by { rfl }
theorem a3(): 100000000 % 7 = 2 := by { rfl }
theorem a4(): nat_beq(123456789, 123456789) = true := by { rfl }
theorem a5(): nat_lt(5000000, 4999999) = false := by { rfl }
theorem a6(): 5 - 9 = 0 := by { rfl }
theorem a7(): 7 / 0 = 0 := by { rfl }
theorem a8(): 7 % 0 = 7 := by { rfl }
theorem a9(): 123456 * 654321 = 80779853376 := by { rfl }
theorem big1(): 18446744073709551615 * 18446744073709551615 = 340282366920938463426481119284349108225 := by { rfl }
theorem big2(): nat_pow(2, 100) = 1267650600228229401496703205376 := by { rfl }
