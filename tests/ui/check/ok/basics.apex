fn double(n: Nat) -> Nat { n + n }

fn id<T>(x: T) -> T { x }

fn five() -> Nat { id(5) }

fn local_binding(a: Nat) -> Nat {
    let b := a * 2;
    let c: Nat := b + 1;
    c + a
}

fn pick(c: Bool, a: Nat, b: Nat) -> Nat {
    if c { a } else { b }
}

fn flag() -> Bool { true }

fn linear_id(own x: Nat) -> Nat { x }
