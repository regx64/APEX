// expect: is used before it is defined
trait T { fn a(&self) -> Nat; fn b(&self) -> Nat; }
struct S { x: Nat }
impl T for S {
    fn a(&self) -> Nat { self.b() }
    fn b(&self) -> Nat { self.a() }
}
