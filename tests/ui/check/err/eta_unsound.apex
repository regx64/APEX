// expect: type mismatch
struct Point { x: Nat, y: Nat }
theorem t(a: Nat, b: Nat): Point.mk(a, b) = Point.mk(b, a) := rfl
