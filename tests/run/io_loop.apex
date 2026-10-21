// out: 3
// out: 2
// out: 1
// out: liftoff
fn count_down(n: Nat) -> IO<Unit> {
    match n {
        0 => println("liftoff"),
        Nat.succ(m) => do {
            println(Nat.toString(n));
            count_down(m)
        },
    }
}

fn main() -> IO<Unit> { count_down(3) }
