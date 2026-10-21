// expect: cannot assign to `x` because it is borrowed
fn read(a: &Nat) -> Nat { 0 }
fn f() -> Nat { let mut x := 1; let r := &x; x = 2; read(r) }
