// out: 5050
enum Chain<T> { End, Link(T, Chain<T>) }

fn range(n: Nat) -> Chain<Nat> {
    match n {
        0 => End,
        Nat.succ(m) => Link(n, range(m)),
    }
}

fn sum(c: Chain<Nat>) -> Nat {
    match c {
        End => 0,
        Link(x, rest) => x + sum(rest),
    }
}

fn main() -> Nat { sum(range(100)) }
