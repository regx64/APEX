// expect: cannot derive `Hash`
#[derive(Hash)]
struct P { x: Nat }
