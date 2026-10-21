// out: big
// out: small
fn describe(n: Nat) -> IO<Unit> {
    match n {
        0 => println("small"),
        Nat.succ(_) => println("big"),
    }
}

fn main() -> IO<Unit> {
    do {
        describe(5);
        describe(0)
    }
}
