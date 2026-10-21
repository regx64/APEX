// out: Point(4, 7)
struct Point { x: Nat, y: Nat }

fn shift(p: Point, d: Nat) -> Point { Point.mk(p.x + d, p.y + d) }

fn main() -> Point { shift(Point.mk(1, 4), 3) }
