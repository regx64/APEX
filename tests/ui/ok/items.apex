struct Point { x: Nat, y: Nat }

enum Option<T> { None, Some(T) }

trait Shape {
    fn area(&self) -> Nat;
}

impl Shape for Point {
    fn area(&self) -> Nat { self.x * self.y }
}

fn push<T, n: Nat>(own v: Vec<T, n>, x: T) -> Vec<T, n + 1> {
    v
}

fn first<'a>(v: &'a mut Vec<Nat, n + 1>) -> &'a mut Nat {
    v.get(0)
}

fn pick(c: Bool, a: Nat, b: Nat) -> Nat {
    if c { a } else { b }
}

fn describe(o: Option<Nat>) -> Nat {
    match o {
        None => 0,
        Some(n) => { n + 1 }
    }
}

theorem add_comm(a: Nat, b: Nat): a + b = b + a := by {
    induction a
    simp
}

theorem refl_eq(a: Nat): a = a := rfl
