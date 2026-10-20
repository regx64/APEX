// expect: has no field
struct P { x: Nat }
fn f(p: P) -> Nat { p.z }
