// out: 1
// out: [3, 2]
// out: 3
// out: 6
enum Vec<T>(n: Nat) {
    Nil: Vec<T, 0>,
    Cons<n: Nat>(T, Vec<T, n>): Vec<T, n + 1>,
}

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

fn vmap<A: Type, B: Type, n: Nat>(v: Vec<A, n>, f: A -> B) -> Vec<B, n> {
    match v {
        Vec.Nil => Vec.Nil,
        Vec.Cons(x, rest) => Vec.Cons(f(x), vmap(rest, f)),
    }
}

fn vsum<n: Nat>(v: Vec<Nat, n>) -> Nat {
    match v {
        Vec.Nil => 0,
        Vec.Cons(x, rest) => x + vsum(rest),
    }
}

fn vtolist<T: Type, n: Nat>(v: Vec<T, n>) -> List<T> {
    match v {
        Vec.Nil => List.nil,
        Vec.Cons(x, rest) => List.cons(x, vtolist(rest)),
    }
}

fn main() -> IO<Unit> {
    do {
        let v := Vec.Cons(1, Vec.Cons(2, Vec.Cons(3, Vec.Nil)));
        display(vhead(v));
        display(vtolist(vmap(vtail(Vec.Cons(0, Vec.Cons(2, Vec.Cons(1, Vec.Nil)))), |x: Nat| x + 1)));
        display(vhead(vmap(v, |x: Nat| x * 3)));
        display(vsum(v))
    }
}
