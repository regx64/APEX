// out: 3628800
fn fact(n: Nat) -> Nat {
    match n {
        0 => 1,
        Nat.succ(m) => n * fact(m),
    }
}

fn main() -> Nat { fact(10) }
