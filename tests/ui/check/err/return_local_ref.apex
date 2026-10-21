// expect: cannot return a reference to the local variable `x`
fn f(v: &Nat) -> &Nat { let x := 5; &x }
