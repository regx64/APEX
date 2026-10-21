// dependent pattern matching on indexed families
enum Vec<T>(n: Nat) {
    Nil: Vec<T, 0>,
    Cons<n: Nat>(T, Vec<T, n>): Vec<T, n + 1>,
}

// the `Nil` case is impossible: its index `0` cannot equal `n + 1`
fn vhead<T: Type, n: Nat>(v: Vec<T, n + 1>) -> T {
    match v {
        Vec.Cons(x, rest) => x,
    }
}

fn vtail<T: Type, n: Nat>(v: Vec<T, n + 1>) -> Vec<T, n> {
    match v {
        Vec.Cons(x, rest) => rest,
    }
}

fn vlen<T: Type, n: Nat>(v: Vec<T, n>) -> Nat {
    match v {
        Vec.Nil => 0,
        Vec.Cons(x, rest) => 1 + vlen(rest),
    }
}

// two vectors of the same length: the inner match is on `Vec<B, m + 1>`
fn vzip<A: Type, B: Type, n: Nat>(v: Vec<A, n>, w: Vec<B, n>) -> Vec<Prod<A, B>, n> {
    match v {
        Vec.Nil => Vec.Nil,
        Vec.Cons(x, xs) => match w {
            Vec.Cons(y, ys) => Vec.Cons(Prod.mk(x, y), vzip(xs, ys)),
        },
    }
}

fn vmap<A: Type, B: Type, n: Nat>(v: Vec<A, n>, f: A -> B) -> Vec<B, n> {
    match v {
        Vec.Nil => Vec.Nil,
        Vec.Cons(x, rest) => Vec.Cons(f(x), vmap(rest, f)),
    }
}

// the length is part of the type: a theorem about it is by `rfl`
theorem vlen_ex(): vlen(Vec.Cons(5, Vec.Cons(6, Vec.Nil))) = 2 := rfl
theorem vhead_ex(): vhead(Vec.Cons(5, Vec.Cons(6, Vec.Nil))) = 5 := rfl
theorem vmap_ex(): vhead(vmap(Vec.Cons(1, Vec.Nil), |x: Nat| x + 41)) = 42 := rfl

// a proof by dependent matching (a `Prop`-valued result is eliminable from a predicate)
enum Even(n: Nat): Prop {
    Zero: Even(0),
    Add2<k: Nat>(Even(k)): Even(k + 2),
}

theorem le2_add2(k: Nat): le(2, k + 2) := by { omega }

fn even_ge<n: Nat>(h: Even(n)) -> Or<n = 0, le(2, n)> {
    match h {
        Even.Zero => Or.inl(Eq.refl(0)),
        Even.Add2(h2) => Or.inr(le2_add2(_)),
    }
}
