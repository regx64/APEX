// expect: cannot borrow `x` as mutable because it is also borrowed as immutable
fn read(a: &Nat) -> Nat { 0 }
fn bump(a: &mut Nat) { }
fn f() -> Nat { let mut x := 1; let r := &x; bump(&mut x); read(r) }
