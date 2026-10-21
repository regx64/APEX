// expect: store it in a `let mut` variable first
struct S { n: Nat }
impl S { fn bump(&mut self) { self.n += 1; } }
fn f() -> Nat { S.mk(1).bump(); 0 }
