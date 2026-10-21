// expect: but the trait requires
trait Shape { fn area(&self) -> Nat; }
struct S { a: Nat }
impl Shape for S { fn area(&self) -> String { "x" } }
