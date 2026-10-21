// expect: cannot be partially applied
fn add_to(a: &mut Nat, n: Nat) { a += n; }
fn f() -> Nat { let mut x := 1; let g := add_to(&mut x); 0 }
