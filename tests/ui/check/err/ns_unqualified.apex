// expect: unknown identifier
namespace A { fn f(n: Nat) -> Nat { n } }
theorem t(): f(1) = 1 := rfl
