universe u v;
fn idu<A: Type(u)>(a: A) -> A { a }
fn const2<A: Type(u), B: Type(v)>(a: A, b: B) -> A { a }
theorem t1(): idu(3) = 3 := by { rfl }
theorem t2(): idu(Nat) = Nat := by { rfl }
theorem t3(): const2(Nat, 5) = Nat := by { rfl }
theorem t4(): const2(2, Nat) = 2 := by { rfl }
fn compose<A: Type(u), B: Type(v), C: Type(u)>(f: B -> C, g: A -> B, x: A) -> C { f(g(x)) }
theorem t5(): compose(|n: Nat| n + 1, |n: Nat| n * 2, 3) = 7 := by { rfl }
