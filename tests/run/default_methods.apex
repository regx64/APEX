// out: 7
// out: false
// out: 999
// out: 5
// out: 13
trait Container {
    fn size(&self) -> Nat;
    fn fold<B>(&self, init: B, step: Nat -> B -> B) -> B;
    fn total(&self) -> Nat { self.fold(0, |n, acc| n + acc) }
    fn is_empty(&self) -> Bool { self.size() == 0 }
}

struct Pair { a: Nat, b: Nat }

impl Container for Pair {
    fn size(&self) -> Nat { 2 }
    fn fold<B>(&self, init: B, step: Nat -> B -> B) -> B { step(self.b, step(self.a, init)) }
}

struct Empty { x: Nat }

impl Container for Empty {
    fn size(&self) -> Nat { 0 }
    fn fold<B>(&self, init: B, step: Nat -> B -> B) -> B { init }
    fn total(&self) -> Nat { 999 }
}

fn count_total<C: Container>(c: C) -> Nat { c.total() + c.size() }

// a method may use a sibling declared later in the trait
trait Order { fn first(&self) -> Nat; fn second(&self) -> Nat; }
struct S { x: Nat }
impl Order for S {
    fn first(&self) -> Nat { self.second() + 1 }
    fn second(&self) -> Nat { self.x * 3 }
}

fn main() -> IO<Unit> {
    do {
        display(Pair.mk(3, 4).total());
        display(Pair.mk(3, 4).is_empty());
        display(Empty.mk(0).total());
        display(count_total(Pair.mk(1, 2)));
        display(S.mk(4).first());
    }
}
