// out: 99999
// A match that ignores the recursive result must not walk the whole number.
fn pred(n: Nat) -> Nat {
    match n {
        0 => 0,
        Nat.succ(m) => m,
    }
}

fn main() -> Nat { pred(100000) }
