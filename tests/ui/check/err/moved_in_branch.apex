// expect: use of moved value `x`
fn consume(own a: Nat) -> Nat { a }
fn f(own x: Nat) -> Nat { if true { consume(x) } else { 0 } + consume(x) }
