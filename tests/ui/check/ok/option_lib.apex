fn find_first(xs: List<Nat>) -> Option<Nat> {
    match xs { List.nil => Option.None, List.cons(x, _) => Option.Some(x) }
}
theorem f1(): find_first([3, 4]) = Option.Some(3) := by { rfl }
theorem f2(): option_get_or(find_first([]), 7) = 7 := by { rfl }
fn pos(n: Nat, h: lt(0, n)) -> Subtype<Nat, (|m: Nat| lt(0, m))> { Subtype.mk(n, h) }
theorem p1(): Subtype.val(pos(3, by { omega })) = 3 := by { rfl }
