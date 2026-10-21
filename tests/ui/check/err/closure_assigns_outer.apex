// expect: not declared `mut`
fn f() -> Nat { let mut x := 1; let g := |n: Nat| { x = n; n }; 0 }
