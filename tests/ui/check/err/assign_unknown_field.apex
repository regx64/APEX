// expect: has no field `z`
struct P { x: Nat }
fn f() -> Nat { let mut p := P.mk(1); p.z = 2; 0 }
