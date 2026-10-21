// out: 6765
// out: 1597
fn fib(n: Nat) -> Nat {
    match n {
        0 => 0,
        1 => 1,
        Nat.succ(Nat.succ(m)) => fib(m) + fib(Nat.succ(m)),
    }
}

fn main() -> IO<Unit> {
    do {
        println(Nat.toString(fib(20)));
        println(Nat.toString(fib(17)))
    }
}
