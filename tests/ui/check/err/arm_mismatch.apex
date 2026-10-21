// expect: type mismatch
fn f(n: Nat) -> Nat { match n { 0 => true, _ => 1 } }
