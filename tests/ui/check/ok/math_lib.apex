theorem t1(): dvd(3, 12) := by { exists 4 }
theorem t2(n: Nat): 2 * sum_to(n) = n * (n + 1) := gauss(n)
theorem t3(a: Nat, b: Nat, c: Nat, h: dvd(a, b)): dvd(a, b * c) := dvd_of_dvd_mul(a, b, c, h)
theorem t4(): fib(10) = 55 := by { rfl }
theorem t5(n: Nat): Or<is_even(n), is_odd(n)> := even_or_odd(n)
