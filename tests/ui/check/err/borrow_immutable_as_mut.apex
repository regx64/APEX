// expect: not declared `mut`
fn inc(n: &mut Nat) { n += 1; }
fn f() -> Nat { let x := 1; inc(&mut x); x }
