// expect: expected a reference, found a value
fn read(a: &Nat) -> Nat { 0 }
fn f() -> Nat { read(5) }
