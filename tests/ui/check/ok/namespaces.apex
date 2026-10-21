namespace Arith {
    fn double(n: Nat) -> Nat { n + n }
    theorem double_eq(n: Nat): double(n) = n + n := by { rfl }

    namespace Inner {
        fn triple(n: Nat) -> Nat { double(n) + n }
        theorem triple_zero(): triple(0) = 0 := rfl
    }
}

theorem outside(): Arith.double(2) = 4 := rfl
theorem nested(): Arith.Inner.triple(1) = 3 := rfl

open Arith;
theorem opened(): double(3) = 6 := rfl

section {
    variable (n: Nat);
    open Arith.Inner;
    theorem sec_triple(): triple(n) = double(n) + n := by { rfl }
    fn twice_plus(m: Nat) -> Nat { n + m + m }
}
theorem sec_use(): Arith.Inner.triple(2) = Arith.double(2) + 2 := sec_triple(2)
theorem twice_use(): twice_plus(1, 2) = 5 := rfl

// shadowing a prelude name inside a namespace does not disturb the prelude
namespace Mine {
    theorem add_comm(a: Nat, b: Nat): a + b = b + a := by { simp [add_comm] }
}
theorem prelude_still_there(a: Nat, b: Nat): a + b = b + a := add_comm(a, b)
