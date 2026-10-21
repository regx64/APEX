// out: done
// 50000 iterations of a monadic loop must not overflow the stack
fn spin(n: Nat) -> IO<Unit> {
    match n {
        0 => println("done"),
        Nat.succ(m) => do { pure(()); spin(m) },
    }
}

fn main() -> IO<Unit> { spin(50000) }
