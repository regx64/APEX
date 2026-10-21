// out: Some(5)
enum Option<T> { None, Some(T) }

fn safe_pred(n: Nat) -> Option<Nat> {
    match n {
        0 => None,
        Nat.succ(m) => Some(m),
    }
}

fn main() -> Option<Nat> { safe_pred(6) }
