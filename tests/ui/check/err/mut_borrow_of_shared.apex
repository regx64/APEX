// expect: it is behind a `&` reference
fn bump(a: &mut Nat) { }
fn f(x: &Nat) -> Nat { bump(&mut x); 0 }
