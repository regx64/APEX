trait Scale<B, out C> { fn scale(self, k: B) -> C; }
struct Vec2 { x: Nat, y: Nat }
impl Scale<Nat, Vec2> for Vec2 {
    fn scale(self, k: Nat) -> Vec2 { Vec2.mk(self.x * k, self.y * k) }
}
impl Scale<Nat, Nat> for Nat {
    fn scale(self, k: Nat) -> Nat { self * k }
}
fn twice(v: Vec2) -> Vec2 { v.scale(2) }
theorem t1(): twice(Vec2.mk(1, 2)).y = 4 := by { rfl }
fn n6() -> Nat { (3 : Nat).scale(2) }
theorem t2(): n6() = 6 := by { rfl }
fn second(v: Vec2) -> Nat { v.scale(2).y }
theorem t3(): second(Vec2.mk(1, 5)) = 10 := by { rfl }
