// expect: no implementation of `Shape Nat`
trait Shape { fn area(&self) -> Nat; }
fn describe<T: Shape>(x: T) -> Nat { x.area() }
fn f() -> Nat { describe(5) }
