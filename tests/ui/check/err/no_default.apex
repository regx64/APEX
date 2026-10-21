// expect: missing method `b`
trait T { fn a(&self) -> Nat; fn b(&self) -> Nat; }
struct S { x: Nat }
impl T for S { fn a(&self) -> Nat { 1 } }
