// expect: storing a `&mut` reference in a variable is not supported yet
fn f() -> Nat { let mut x := 1; let r := &mut x; 0 }
