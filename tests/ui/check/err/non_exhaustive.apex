// expect: non-exhaustive patterns: missing `Option.None`
enum Option<T> { None, Some(T) }
fn f(o: Option<Nat>) -> Nat { match o { Some(x) => x } }
