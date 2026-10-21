// expect: but the trait requires
trait T { fn m<B>(&self, b: B) -> B; }
struct S { x: Nat }
impl T for S { fn m(&self, b: Nat) -> Nat { b } }
