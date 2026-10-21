// expect: cannot have `&mut` parameters yet
fn count(n: Nat, acc: &mut Nat) { match n { 0 => {} Nat.succ(m) => { acc += 1; count(m, acc); } } }
