// out: 7
// Types, proofs and erased arguments have no runtime content.
theorem three_eq(): 1 + 2 = 3 := rfl

fn id<T>(x: T) -> T { x }

fn main() -> Nat { id(3) + id(4) }
