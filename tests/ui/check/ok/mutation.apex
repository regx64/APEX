// Mutation is elaborated to pure terms, so functions that mutate can be proved about.
struct Counter { n: Nat, step: Nat }
struct Outer { inner: Counter, label: Nat }

fn bump(n: Nat) -> Nat {
    let mut t := n;
    if n > 3 { t += 1; } else { t = 0; }
    t
}

fn classify(n: Nat) -> Nat {
    let mut r := 0;
    match n {
        0 => { r = 10; }
        Nat.succ(m) => { r = m + 20; }
    }
    r
}

fn sum_to_three() -> Nat {
    let mut acc := 0;
    acc += 1;
    acc += 2;
    acc *= 3;
    acc
}

fn nested() -> Nat {
    let mut o := Outer.mk(Counter.mk(1, 2), 9);
    o.inner.n = o.inner.n + 40;
    o.label = 0;
    o.inner.n + o.label
}

fn two_vars(n: Nat) -> Nat {
    let mut a := 1;
    let mut b := 10;
    if n > 2 { a += 1; b += 5; }
    a * 100 + b
}

fn else_if(n: Nat) -> Nat {
    let mut t := 0;
    if n > 9 { t = 1; } else if n > 3 { t = 2; } else { t = 3; }
    t
}

theorem bump_hi(): bump(5) = 6 := rfl
theorem bump_lo(): bump(2) = 0 := rfl
theorem classify_zero(): classify(0) = 10 := rfl
theorem classify_succ(): classify(5) = 24 := rfl
theorem sum_ex(): sum_to_three() = 9 := rfl
theorem nested_ex(): nested() = 41 := rfl
theorem two_vars_hi(): two_vars(3) = 215 := rfl
theorem two_vars_lo(): two_vars(1) = 110 := rfl
theorem else_if_ex(): else_if(5) = 2 := rfl
