// out: 5000050000
// 100000 nested calls, and an accumulator that is a chain of 100000 pending additions
fn sum_to(n: Nat, acc: Nat) -> Nat {
    match n {
        0 => acc,
        Nat.succ(m) => sum_to(m, acc + n),
    }
}

fn main() -> Nat { sum_to(100000, 0) }
