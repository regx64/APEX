// expect: use of moved value `x`
fn consume(own a: Nat) -> Nat { a }
fn f(own x: Nat) -> Nat { consume(x) + consume(x) }
