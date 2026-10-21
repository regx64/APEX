// Surface-level prelude, elaborated at startup.

/// Pairs. The compiler threads `&mut` arguments and variables assigned in branches through
/// `Prod`: a call returns `(result, updated arguments)`.
struct Prod<A, B> { fst: A, snd: B }

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

// Division by repeated subtraction, with the dividend as fuel (each step removes at
// least one, so `a + 1` steps always suffice). Division by zero is zero, and
// `a % 0` is `a`, as in Lean.
fn nat_div_aux(fuel: Nat, a: Nat, b: Nat) -> Nat {
    match fuel {
        0 => 0,
        Nat.succ(f) => if nat_lt(a, b) { 0 } else { Nat.succ(nat_div_aux(f, nat_sub(a, b), b)) },
    }
}

fn nat_div(a: Nat, b: Nat) -> Nat {
    if nat_is_zero(b) { 0 } else { nat_div_aux(Nat.succ(a), a, b) }
}

fn nat_rem(a: Nat, b: Nat) -> Nat {
    if nat_is_zero(b) { a } else { nat_sub(a, Nat.mul(nat_div(a, b), b)) }
}

// ---- operator traits ----

trait Add { fn add(self, other: Self) -> Self; }
trait Sub { fn sub(self, other: Self) -> Self; }
trait Mul { fn mul(self, other: Self) -> Self; }
trait Div { fn div(self, other: Self) -> Self; }
trait Rem { fn rem(self, other: Self) -> Self; }
trait BEq { fn beq(self, other: Self) -> Bool; }
trait Ord { fn lt(self, other: Self) -> Bool; }
trait Show { fn show(&self) -> String; }

impl Add for Nat { fn add(self, other: Self) -> Self { Nat.add(self, other) } }
impl Sub for Nat { fn sub(self, other: Self) -> Self { nat_sub(self, other) } }
impl Mul for Nat { fn mul(self, other: Self) -> Self { Nat.mul(self, other) } }
impl Div for Nat { fn div(self, other: Self) -> Self { nat_div(self, other) } }
impl Rem for Nat { fn rem(self, other: Self) -> Self { nat_rem(self, other) } }
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

// ---- lists ----

fn range_from(start: Nat, count: Nat) -> List<Nat> {
    match count {
        0 => List.nil,
        Nat.succ(c) => List.cons(start, range_from(Nat.succ(start), c)),
    }
}

/// `range(n)` is `[0, 1, .., n - 1]`.
fn range(n: Nat) -> List<Nat> { range_from(0, n) }

fn list_len<T>(xs: List<T>) -> Nat {
    match xs {
        List.nil => 0,
        List.cons(_, rest) => 1 + list_len(rest),
    }
}

fn list_append<T>(xs: List<T>, ys: List<T>) -> List<T> {
    match xs {
        List.nil => ys,
        List.cons(x, rest) => List.cons(x, list_append(rest, ys)),
    }
}

fn list_map<A, B>(xs: List<A>, f: A -> B) -> List<B> {
    match xs {
        List.nil => List.nil,
        List.cons(x, rest) => List.cons(f(x), list_map(rest, f)),
    }
}

fn list_filter<A>(xs: List<A>, keep: A -> Bool) -> List<A> {
    match xs {
        List.nil => List.nil,
        List.cons(x, rest) => if keep(x) {
            List.cons(x, list_filter(rest, keep))
        } else {
            list_filter(rest, keep)
        },
    }
}

fn list_foldl<A, B>(xs: List<A>, init: B, f: B -> A -> B) -> B {
    match xs {
        List.nil => init,
        List.cons(x, rest) => list_foldl(rest, f(init, x), f),
    }
}

fn list_sum(xs: List<Nat>) -> Nat {
    match xs {
        List.nil => 0,
        List.cons(x, rest) => x + list_sum(rest),
    }
}

fn list_reverse_onto<T>(xs: List<T>, acc: List<T>) -> List<T> {
    match xs {
        List.nil => acc,
        List.cons(x, rest) => list_reverse_onto(rest, List.cons(x, acc)),
    }
}

fn list_reverse<T>(xs: List<T>) -> List<T> { list_reverse_onto(xs, List.nil) }

/// The loop behind `for x in xs { .. }`.
fn for_each<T>(xs: List<T>, f: T -> IO<Unit>) -> IO<Unit> {
    match xs {
        List.nil => pure(()),
        List.cons(x, rest) => do {
            f(x);
            for_each(rest, f)
        },
    }
}

fn list_items<T: Show>(xs: List<T>) -> String {
    match xs {
        List.nil => "",
        List.cons(x, rest) => match rest {
            List.nil => x.show(),
            _ => String.append(x.show(), String.append(", ", list_items(rest))),
        },
    }
}

impl<T: Show> Show for List<T> {
    fn show(&self) -> String { String.append("[", String.append(list_items(self), "]")) }
}

// ---- theorem library: facts about Nat arithmetic, proved with tactics ----
// Theorems marked #[simp] are the default rewrite rules of the `simp` tactic.

#[simp]
theorem add_zero(n: Nat): n + 0 = n := by { rfl }

#[simp]
theorem add_succ(n: Nat, m: Nat): n + Nat.succ(m) = Nat.succ(n + m) := by { rfl }

#[simp]
theorem zero_add(n: Nat): 0 + n = n := by {
    induction n with {
        zero => { rfl },
        succ(m, ih) => { simp [ih] },
    }
}

#[simp]
theorem succ_add(n: Nat, m: Nat): Nat.succ(n) + m = Nat.succ(n + m) := by {
    induction m with {
        zero => { rfl },
        succ(k, ih) => { simp [ih] },
    }
}

theorem add_comm(a: Nat, b: Nat): a + b = b + a := by {
    induction b with {
        zero => { simp },
        succ(k, ih) => { simp [ih] },
    }
}

theorem add_assoc(a: Nat, b: Nat, c: Nat): (a + b) + c = a + (b + c) := by {
    induction c with {
        zero => { rfl },
        succ(k, ih) => { simp [ih] },
    }
}

#[simp]
theorem mul_zero(n: Nat): n * 0 = 0 := by { rfl }

#[simp]
theorem mul_succ(n: Nat, m: Nat): n * Nat.succ(m) = n * m + n := by { rfl }

#[simp]
theorem zero_mul(n: Nat): 0 * n = 0 := by {
    induction n with {
        zero => { rfl },
        succ(m, ih) => { simp [ih] },
    }
}

#[simp]
theorem succ_mul(n: Nat, m: Nat): Nat.succ(n) * m = n * m + m := by {
    induction m with {
        zero => { rfl },
        succ(k, ih) => {
            simp [ih];
            rw [add_assoc, add_assoc, add_comm(k, n)]
        },
    }
}

#[simp]
theorem mul_one(n: Nat): n * 1 = n := by { simp }

#[simp]
theorem one_mul(n: Nat): 1 * n = n := by {
    induction n with {
        zero => { rfl },
        succ(m, ih) => { simp [ih] },
    }
}

theorem mul_comm(a: Nat, b: Nat): a * b = b * a := by {
    induction b with {
        zero => { simp },
        succ(k, ih) => { simp [ih] },
    }
}
