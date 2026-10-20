enum Color { Red, Green, Blue }

enum Option<T> { None, Some(T) }

enum Chain<T> { End, Link(T, Chain<T>) }

struct Point { x: Nat, y: Nat }

struct Pair<A, B> { first: A, second: B }

fn favorite() -> Color { Color.Green }

fn some_five() -> Option<Nat> { Some(5) }

fn none_nat() -> Option<Nat> { None }

fn two_chain() -> Chain<Nat> { Link(1, Link(2, End)) }

fn origin() -> Point { Point.mk(0, 0) }

fn sum(p: Point) -> Nat { p.x + p.y }

fn swap_first(p: Pair<Nat, Bool>) -> Nat { p.first }
