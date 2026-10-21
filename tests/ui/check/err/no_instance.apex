// expect: no implementation of `Show Square`
struct Square { side: Nat }
fn f() -> String { Show.show(Square.mk(1)) }
