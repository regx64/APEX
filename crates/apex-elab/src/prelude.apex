// Surface-level prelude, elaborated at startup.

theorem rfl<A: Type, a: A>(): a = a := Eq.refl(a)

fn println(s: String) -> IO<Unit> {
    do {
        print(s);
        print("\n")
    }
}

// ---- natural number helpers (the interpreter replaces nat_sub / nat_beq / nat_lt
// with native versions; these definitions are what proofs see) ----

fn nat_pred(n: Nat) -> Nat {
    match n {
        0 => 0,
        Nat.succ(m) => m,
    }
}

fn nat_is_zero(n: Nat) -> Bool {
    match n {
        0 => true,
        _ => false,
    }
}

fn nat_is_succ(n: Nat) -> Bool {
    match n {
        0 => false,
        _ => true,
    }
}

fn nat_sub(a: Nat, b: Nat) -> Nat {
    match b {
        0 => a,
        Nat.succ(m) => nat_pred(nat_sub(a, m)),
    }
}

fn nat_beq(a: Nat, b: Nat) -> Bool {
    match a {
        0 => nat_is_zero(b),
        Nat.succ(n) => match b {
            0 => false,
            Nat.succ(m) => nat_beq(n, m),
        },
    }
}

fn nat_lt(a: Nat, b: Nat) -> Bool {
    match a {
        0 => nat_is_succ(b),
        Nat.succ(n) => match b {
            0 => false,
            Nat.succ(m) => nat_lt(n, m),
        },
    }
}

// ---- operator traits ----

trait Add { fn add(self, other: Self) -> Self; }
trait Sub { fn sub(self, other: Self) -> Self; }
trait Mul { fn mul(self, other: Self) -> Self; }
trait BEq { fn beq(self, other: Self) -> Bool; }
trait Ord { fn lt(self, other: Self) -> Bool; }
trait Show { fn show(&self) -> String; }

impl Add for Nat { fn add(self, other: Self) -> Self { Nat.add(self, other) } }
impl Sub for Nat { fn sub(self, other: Self) -> Self { nat_sub(self, other) } }
impl Mul for Nat { fn mul(self, other: Self) -> Self { Nat.mul(self, other) } }
impl BEq for Nat { fn beq(self, other: Self) -> Bool { nat_beq(self, other) } }
impl Ord for Nat { fn lt(self, other: Self) -> Bool { nat_lt(self, other) } }
impl Add for String { fn add(self, other: Self) -> Self { String.append(self, other) } }

impl BEq for Bool {
    fn beq(self, other: Self) -> Bool {
        match self {
            true => other,
            false => match other {
                true => false,
                false => true,
            },
        }
    }
}

impl Show for Nat { fn show(&self) -> String { Nat.toString(self) } }
impl Show for String { fn show(&self) -> String { self } }
impl Show for Unit { fn show(&self) -> String { "()" } }
impl Show for Bool {
    fn show(&self) -> String {
        match self {
            true => "true",
            false => "false",
        }
    }
}

/// Print any `Show` value followed by a newline.
fn display<T: Show>(x: T) -> IO<Unit> { println(x.show()) }
