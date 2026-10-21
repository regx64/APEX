// out: 3
enum Chain<T> { End, Link(T, Chain<T>) }

fn second(c: Chain<Nat>) -> Nat {
    match c {
        Link(_, Link(x, _)) => x,
        _ => 0,
    }
}

fn main() -> Nat { second(Link(1, Link(3, End))) }
