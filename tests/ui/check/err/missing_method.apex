// expect: missing method `name`
trait Shape { fn area(&self) -> Nat; fn name(&self) -> String; }
struct S { a: Nat }
impl Shape for S { fn area(&self) -> Nat { 1 } }
