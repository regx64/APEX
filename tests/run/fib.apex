// out: 832040
fn fib_iter(n: Nat, a: Nat, b: Nat) -> Nat {
    match n {
        0 => a,
        Nat.succ(m) => fib_iter(m, b, a + b),
    }
}

fn main() -> Nat { fib_iter(30, 0, 1) }
