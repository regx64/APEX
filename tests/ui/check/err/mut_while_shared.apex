// expect: cannot borrow `x` as immutable because it is also borrowed as mutable
fn mixed(a: &mut Nat, b: &Nat) { }
fn f() -> Nat { let mut x := 1; mixed(&mut x, &x); x }
