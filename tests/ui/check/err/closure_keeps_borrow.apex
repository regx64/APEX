// expect: cannot assign to `x` because it is borrowed
fn read(a: &Nat) -> Nat { 0 }
fn f() -> Nat { let mut x := 1; let r := &x; let g := |n: Nat| read(r) + n; x = 2; g(1) }
