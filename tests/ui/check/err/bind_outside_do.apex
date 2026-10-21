// expect: only allowed inside a `do` block
fn f() -> Nat { let x <- pure(1); 2 }
