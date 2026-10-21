enum Option<T> { None, Some(T) }

enum Chain<T> { End, Link(T, Chain<T>) }

fn is_zero(n: Nat) -> Bool {
    match n {
        0 => true,
        _ => false,
    }
}

fn pred(n: Nat) -> Nat {
    match n {
        Nat.zero => 0,
        Nat.succ(m) => m,
    }
}

fn unwrap_or(o: Option<Nat>, d: Nat) -> Nat {
    match o {
        None => d,
        Some(x) => x,
    }
}

fn second(c: Chain<Nat>) -> Nat {
    match c {
        Link(_, Link(x, _)) => x,
        _ => 0,
    }
}

fn pred_of_pred(n: Nat) -> Nat {
    match n {
        Nat.succ(Nat.succ(m)) => m,
        _ => 0,
    }
}

fn not(b: Bool) -> Bool {
    match b {
        true => false,
        false => true,
    }
}

theorem pred_ex(): pred(3) = 2 := rfl

theorem is_zero_ex(): is_zero(0) = true := rfl

theorem unwrap_ex(): unwrap_or(Some(7), 0) = 7 := rfl

theorem second_ex(): second(Link(1, Link(2, End))) = 2 := rfl

theorem not_ex(): not(true) = false := rfl
