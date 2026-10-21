// expect: not structural
fn bad(n: Nat) -> Nat { match n { 0 => 0, Nat.succ(m) => bad(Nat.succ(m)) } }
