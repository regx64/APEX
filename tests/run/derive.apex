// out: Point { x: 1, y: 2 }
// out: true
// out: false
// out: Circle(5)
// out: Rect(2, 3)
// out: Origin
// out: true
// out: Pair { fst: 1, snd: true }
// out: 7
// out: Point3 { x: 1, y: 2, z: 3 }
// out: true
#[derive(BEq, Show, Ord)]
struct Point { x: Nat, y: Nat }

#[derive(BEq, Show, Ord)]
enum Shape { Origin, Circle(Nat), Rect(Nat, Nat) }

#[derive(Show)]
struct Pair<A, B> { fst: A, snd: B }

struct Point3 extends Point { z: Nat }

impl Show for Point3 {
    fn show(&self) -> String {
        String.append("Point3 { x: ", String.append(self.x.show(), String.append(", y: ", String.append(self.y.show(), String.append(", z: ", String.append(self.z.show(), " }"))))))
    }
}

fn main() -> IO<Unit> {
    do {
        display(Point.mk(1, 2));
        display(Point.mk(1, 2) == Point.mk(1, 2));
        display(Point.mk(1, 2) == Point.mk(1, 3));
        display(Shape.Circle(5));
        display(Shape.Rect(2, 3));
        display(Shape.Origin);
        display(Shape.Circle(1) < Shape.Rect(0, 0));
        display(Pair.mk(1, true));
        let p3 := Point3.mk(1, 2, 7);
        display(p3.z);
        display(Point3.mk(1, 2, 3));
        display(p3.toPoint() == Point.mk(1, 2))
    }
}
