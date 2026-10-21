// expect: pass `&mut place`
fn inc(n: &mut Nat) { n += 1; }
fn f() -> Nat { let mut x := 1; inc(5); x }
