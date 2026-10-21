// recursion on subterms deeper than a direct field is compiled through `brecOn`
fn fib(n: Nat) -> Nat {
    match n {
        0 => 0,
        1 => 1,
        Nat.succ(Nat.succ(m)) => fib(m) + fib(Nat.succ(m)),
    }
}

fn trib(n: Nat) -> Nat {
    match n {
        0 => 0,
        1 => 0,
        2 => 1,
        Nat.succ(Nat.succ(Nat.succ(m))) => trib(m) + trib(Nat.succ(m)) + trib(Nat.succ(Nat.succ(m))),
    }
}

// the other parameters change on every call
fn fib_acc(n: Nat, a: Nat, b: Nat) -> Nat {
    match n {
        0 => a,
        Nat.succ(m) => fib_acc(m, b, a + b),
    }
}

// two steps at a time over a list
fn sum_pairs(xs: List<Nat>) -> Nat {
    match xs {
        List.nil => 0,
        List.cons(a, rest) => match rest {
            List.nil => a,
            List.cons(b, more) => a + b + sum_pairs(more),
        },
    }
}

// skipping the tail's head: the call is on the tail of the tail
fn every_other(xs: List<Nat>) -> Nat {
    match xs {
        List.nil => 0,
        List.cons(a, rest) => match rest {
            List.nil => a,
            List.cons(b, more) => a + every_other(more),
        },
    }
}

theorem fib_ex(): fib(10) = 55 := rfl
theorem trib_ex(): trib(7) = 13 := rfl
theorem fib_acc_ex(): fib_acc(10, 0, 1) = 55 := rfl
theorem sum_pairs_ex(): sum_pairs([1, 2, 3, 4, 5]) = 15 := rfl
theorem every_other_ex(): every_other([1, 2, 3, 4, 5]) = 9 := rfl
