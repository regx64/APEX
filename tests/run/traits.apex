// out: 5
// out: text
// out: true
// out: square: 9
// out: rect: 10
// out: Some 7
// out: None
// out: square
// out: 25
// out: lt
// out: 7
// out: 1
// out: 5 + 0
trait Shape {
    fn area(&self) -> Nat;
    fn name(&self) -> String;
}

struct Square { side: Nat }
struct Rect { w: Nat, h: Nat }

impl Shape for Square {
    fn area(&self) -> Nat { self.side * self.side }
    fn name(&self) -> String { "square" }
}

impl Shape for Rect {
    fn area(&self) -> Nat { self.w * self.h }
    fn name(&self) -> String { "rect" }
}

fn describe<T: Shape>(x: T) -> String {
    String.append(x.name(), String.append(": ", Nat.toString(x.area())))
}

enum Option<T> { None, Some(T) }

impl<T: Show> Show for Option<T> {
    fn show(&self) -> String {
        match self {
            None => "None",
            Some(x) => String.append("Some ", x.show()),
        }
    }
}

struct Point { x: Nat, y: Nat }

impl Point {
    fn sum(&self) -> Nat { self.x + self.y }
}

trait Default { fn default() -> Self; }
impl Default for Nat { fn default() -> Self { 0 } }

trait Convert<T> { fn convert(self) -> T; }
impl Convert<Nat> for Bool {
    fn convert(self) -> Nat {
        match self {
            true => 1,
            false => 0,
        }
    }
}

fn show_twice<T: Show + Default>(x: T) -> String {
    String.append(x.show(), String.append(" + ", T.default().show()))
}

fn main() -> IO<Unit> {
    do {
        display(5);
        display("text");
        display(true);
        println(describe(Square.mk(3)));
        println(describe(Rect.mk(2, 5)));
        display(Some(7));
        let none: Option<Nat> := None;
        display(none);
        println(Square.mk(4).name());
        let s := Square.mk(5);
        display(s.area());
        if 3 < 5 { println("lt") } else { println("ge") };
        display(Point.mk(3, 4).sum());
        display(true.convert() + 0);
        println(show_twice(5))
    }
}
