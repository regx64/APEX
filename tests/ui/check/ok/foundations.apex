// division and remainder
theorem div_ex(): 7 / 2 = 3 := rfl
theorem rem_ex(): 10 % 3 = 1 := rfl
theorem div_zero(): 5 / 0 = 0 := rfl
theorem rem_zero(): 5 % 0 = 5 := rfl
theorem div_exact(): 12 / 4 = 3 := rfl

// lists, ranges and the list library
theorem len_ex(): list_len([1, 2, 3]) = 3 := rfl
theorem sum_range(): list_sum(range(5)) = 10 := rfl
theorem map_ex(): list_sum(list_map([1, 2, 3], |x| x * 2)) = 12 := rfl
theorem filter_ex(): list_len(list_filter(range(10), |x| x % 2 == 0)) = 5 := rfl
theorem fold_ex(): list_foldl([1, 2, 3, 4], 0, |acc, x| acc + x) = 10 := rfl
theorem rev_ex(): list_reverse([1, 2, 3]) = [3, 2, 1] := rfl

// closures: parameter types from the expected type, or annotated
fn twice(f: Nat -> Nat, x: Nat) -> Nat { f(f(x)) }

fn four() -> Nat { twice(|n| n + 1, 2) }

fn annotated() -> Nat -> Nat { |n: Nat| n * 3 }

fn compose(f: Nat -> Nat, g: Nat -> Nat) -> Nat -> Nat { |x| f(g(x)) }

theorem closure_ex(): twice(|n| n + 1, 2) = 4 := rfl
theorem compose_ex(): compose(|a| a + 1, |b| b * 2)(5) = 11 := rfl

// method generics and default methods
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
    // overrides the default
    fn total(&self) -> Nat { 999 }
}

fn count_total<C: Container>(c: C) -> Nat { c.total() + c.size() }

theorem pair_total(): Pair.mk(3, 4).total() = 7 := rfl
theorem pair_not_empty(): Pair.mk(3, 4).is_empty() = false := rfl
theorem empty_is_empty(): Empty.mk(0).is_empty() = true := rfl
theorem empty_total_overridden(): Empty.mk(0).total() = 999 := rfl
theorem generic_bound(): count_total(Pair.mk(1, 2)) = 5 := rfl
