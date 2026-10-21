// expect: is not a method of `Shape`
trait Shape { fn area(&self) -> Nat; }
struct S { a: Nat }
impl Shape for S { fn area(&self) -> Nat { 1 } fn extra(&self) -> Nat { 2 } }
