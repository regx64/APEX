infixl 65 "+++" => add3;
prefix 100 "~~" => dbl;
macro sq(x) => x * x;
fn add3(a: Nat, b: Nat) -> Nat { a + b + 1 }
fn dbl(a: Nat) -> Nat { a + a }

// declared operators and macros work inside tactic blocks too
theorem t1(): 2 +++ 3 = 6 := by { rfl }
theorem t2(n: Nat): ~~ n = n + n := by { rfl }
theorem t3(n: Nat): sq(n) = n * n := by { rfl }
theorem t4(a: Nat, b: Nat): a +++ b = b +++ a := by { simp [add3]; omega }
