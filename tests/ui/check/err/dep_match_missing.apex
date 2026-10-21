// expect: non-exhaustive patterns: missing `Cons`
enum Vec<T>(n: Nat) {
    Nil: Vec<T, 0>,
    Cons<n: Nat>(T, Vec<T, n>): Vec<T, n + 1>,
}
fn f<n: Nat>(v: Vec<Nat, n>) -> Nat {
    match v {
        Vec.Nil => 0,
    }
}
