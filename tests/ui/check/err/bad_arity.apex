// expect: takes 1 fields
fn f(n: Nat) -> Nat { match n { Nat.succ(a, b) => 0, _ => 1 } }
