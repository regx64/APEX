enum Chain<T> { End, Link(T, Chain<T>) }

fn fact(n: Nat) -> Nat {
    match n {
        0 => 1,
        Nat.succ(m) => n * fact(m),
    }
}

fn add2(a: Nat, b: Nat) -> Nat {
    match a {
        0 => b,
        Nat.succ(m) => Nat.succ(add2(m, b)),
    }
}

fn len<T>(c: Chain<T>) -> Nat {
    match c {
        End => 0,
        Link(_, rest) => 1 + len(rest),
    }
}

fn sum(c: Chain<Nat>) -> Nat {
    match c {
        End => 0,
        Link(x, rest) => x + sum(rest),
    }
}

fn append<T>(a: Chain<T>, b: Chain<T>) -> Chain<T> {
    match a {
        End => b,
        Link(x, rest) => Link(x, append(rest, b)),
    }
}

// the accumulator changes between calls
fn sum_to(n: Nat, acc: Nat) -> Nat {
    match n {
        0 => acc,
        Nat.succ(m) => sum_to(m, acc + n),
    }
}

// recurse on the second parameter
fn mul_by_adding(a: Nat, b: Nat) -> Nat {
    match b {
        0 => 0,
        Nat.succ(m) => a + mul_by_adding(a, m),
    }
}

theorem fact_ex(): fact(3) = 6 := rfl

theorem add2_ex(): add2(2, 2) = 4 := rfl

theorem len_ex(): len(Link(1, Link(2, End))) = 2 := rfl

theorem sum_ex(): sum(Link(1, Link(2, Link(3, End)))) = 6 := rfl

theorem sum_to_ex(): sum_to(3, 0) = 6 := rfl

theorem mul_ex(): mul_by_adding(3, 4) = 12 := rfl

theorem append_ex(): len(append(Link(1, End), Link(2, End))) = 2 := rfl
