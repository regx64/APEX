// expect: takes `&mut`, but a shared reference
fn inc(n: &mut Nat) { n += 1; }
fn f() -> Nat { let mut x := 1; inc(&x); x }
