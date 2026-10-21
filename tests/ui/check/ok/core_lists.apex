// the core library is loaded because these lemmas are named
theorem len_twice(xs: List<Nat>): list_len(list_append(xs, xs)) = list_len(xs) + list_len(xs) := list_len_append(xs, xs)

theorem rev_len(xs: List<Nat>): list_len(list_reverse(xs)) = list_len(xs) := list_len_reverse(xs)

theorem map_len(xs: List<Nat>): list_len(list_map(xs, |x: Nat| x + 1)) = list_len(xs) := list_len_map(xs, |x: Nat| x + 1)

theorem sum_two(xs: List<Nat>, ys: List<Nat>, zs: List<Nat>): list_sum(list_append(list_append(xs, ys), zs)) = list_sum(xs) + list_sum(ys) + list_sum(zs) := by {
    rw [list_append_assoc, list_sum_append, list_sum_append];
    omega
}

theorem range_len_ex(): list_len(range(5)) = 5 := rfl
theorem range_len(n: Nat): list_len(range(n)) = n := list_len_range(n)
