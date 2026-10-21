// out: 6
// out: 10
// out: 5
// out: 100
// out: small
// out: 7
// out: 12
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

fn main() -> IO<Unit> {
    do {
        let mut x := 1;
        x = x + 2;
        x += 3;
        display(x);
        let mut total := 0;
        total += 4;
        if x > 5 { total += 6; } else { total = 0; }
        display(total);
        let mut c := Counter.mk(0, 5);
        c.n = c.n + c.step;
        display(c.n);
        match x {
            6 => { x = 100; }
            _ => { x = 0; }
        }
        display(x);
        // a branch that also prints
        if total > 100 {
            println("big");
        } else {
            println("small");
            total += 1;
        }
        let mut o := Outer.mk(Counter.mk(1, 2), 9);
        o.inner.n = 7;
        display(o.inner.n);
        display(bump(5) + classify(0) - 4);
    }
}
