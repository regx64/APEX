// out: 30
fn main() -> Nat {
    let a := 4;
    let b: Nat := a * 2;
    let c := { let t := b + 1; t * 2 };
    c + 12
}
