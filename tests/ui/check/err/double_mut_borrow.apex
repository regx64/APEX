// expect: cannot borrow `x` as mutable more than once at a time
fn two(a: &mut Nat, b: &mut Nat) { }
fn f() -> Nat { let mut x := 1; two(&mut x, &mut x); x }
