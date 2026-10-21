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

// a bound: callers must supply an instance
fn describe<T: Shape>(x: T) -> String {
    String.append(x.name(), String.append(": ", Nat.toString(x.area())))
}

// inherent methods
struct Point { x: Nat, y: Nat }

impl Point {
    fn sum(&self) -> Nat { self.x + self.y }
    fn shifted(&self, d: Nat) -> Point { Point.mk(self.x + d, self.y + d) }
}

// a conditional impl: Option<T> is Show when T is
enum Option<T> { None, Some(T) }

impl<T: Show> Show for Option<T> {
    fn show(&self) -> String {
        match self {
            None => "None",
            Some(x) => String.append("Some ", x.show()),
        }
    }
}

// a trait without a self parameter: the instance is chosen by the expected type
trait Default { fn default() -> Self; }
impl Default for Nat { fn default() -> Self { 0 } }
impl Default for Bool { fn default() -> Self { false } }

fn zero_nat() -> Nat { Default.default() }

// a trait with a type parameter
trait Convert<T> { fn convert(self) -> T; }
impl Convert<Nat> for Bool {
    fn convert(self) -> Nat {
        match self {
            true => 1,
            false => 0,
        }
    }
}

fn bool_to_nat(b: Bool) -> Nat { b.convert() }

// multiple bounds
fn show_twice<T: Show + Default>(x: T) -> String {
    String.append(x.show(), T.default().show())
}

theorem add_via_trait(): 2 + 3 = 5 := rfl
theorem beq_via_trait(): (2 + 3 == 5) = true := rfl
theorem lt_via_trait(): (2 < 5) = true := rfl
theorem sub_via_trait(): 3 - 5 = 0 := rfl
theorem square_area(): Square.mk(4).area() = 16 := rfl
theorem point_sum(): Point.mk(1, 2).sum() = 3 := rfl
