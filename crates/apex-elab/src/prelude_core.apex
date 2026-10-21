// Verified facts about the list functions of the prelude and about `range`.
theorem list_append_nil<T>(xs: List<T>): list_append(xs, List.nil) = xs := by {
    induction xs with {
        nil => { rfl },
        cons(x, rest, ih) => { simp [list_append, ih] },
    }
}
theorem list_append_assoc<T>(xs: List<T>, ys: List<T>, zs: List<T>): list_append(list_append(xs, ys), zs) = list_append(xs, list_append(ys, zs)) := by {
    induction xs with {
        nil => { rfl },
        cons(x, rest, ih) => { simp [list_append, ih] },
    }
}
theorem list_len_append<T>(xs: List<T>, ys: List<T>): list_len(list_append(xs, ys)) = list_len(xs) + list_len(ys) := by {
    induction xs with {
        nil => { simp [list_len, list_append] },
        cons(x, rest, ih) => { simp_arith [list_len, list_append, ih] },
    }
}
theorem list_len_map<A, B>(xs: List<A>, f: A -> B): list_len(list_map(xs, f)) = list_len(xs) := by {
    induction xs with {
        nil => { rfl },
        cons(x, rest, ih) => { simp [list_len, list_map, ih] },
    }
}
theorem list_map_append<A, B>(xs: List<A>, ys: List<A>, f: A -> B): list_map(list_append(xs, ys), f) = list_append(list_map(xs, f), list_map(ys, f)) := by {
    induction xs with {
        nil => { rfl },
        cons(x, rest, ih) => { simp [list_map, list_append, ih] },
    }
}
theorem list_map_map<A, B, C>(xs: List<A>, f: A -> B, g: B -> C): list_map(list_map(xs, f), g) = list_map(xs, |x: A| g(f(x))) := by {
    induction xs with {
        nil => { rfl },
        cons(x, rest, ih) => { simp [list_map, ih] },
    }
}
theorem list_sum_append(xs: List<Nat>, ys: List<Nat>): list_sum(list_append(xs, ys)) = list_sum(xs) + list_sum(ys) := by {
    induction xs with {
        nil => { simp [list_sum, list_append] },
        cons(x, rest, ih) => { simp_arith [list_sum, list_append, ih] },
    }
}
theorem list_reverse_onto_eq<T>(xs: List<T>, acc: List<T>): list_reverse_onto(xs, acc) = list_append(list_reverse_onto(xs, List.nil), acc) := by {
    induction xs generalizing acc with {
        nil => { rfl },
        cons(x, rest, ih) => {
            simp [list_reverse_onto, ih(List.cons(x, acc)), ih(List.cons(x, List.nil))];
            simp [list_append_assoc, list_append]
        },
    }
}
theorem list_len_reverse_onto<T>(xs: List<T>, acc: List<T>): list_len(list_reverse_onto(xs, acc)) = list_len(xs) + list_len(acc) := by {
    induction xs generalizing acc with {
        nil => { simp [list_len, list_reverse_onto] },
        cons(x, rest, ih) => { simp_arith [list_reverse_onto, ih, list_len] },
    }
}
theorem list_len_reverse<T>(xs: List<T>): list_len(list_reverse(xs)) = list_len(xs) := by {
    simp [list_reverse, list_len_reverse_onto, list_len]
}
theorem list_len_range(n: Nat): list_len(range(n)) = n := by {
    have h: forall(k: Nat, m: Nat) -> list_len(range_from(k, m)) = m := by {
        intro k m;
        induction m generalizing k with {
            zero => { rfl },
            succ(c, ih) => { simp [range_from, list_len, ih] },
        }
    };
    exact h(0, n)
}
theorem list_filter_len_le<T>(xs: List<T>, p: T -> Bool): le(list_len(list_filter(xs, p)), list_len(xs)) := by {
    induction xs with {
        nil => { simp [list_filter, list_len]; exact le_refl(0) },
        cons(x, rest, ih) => {
            cases bool_cases(p(x)) with {
                inl(c) => { simp_arith [list_filter, list_len, c] },
                inr(c) => { simp_arith [list_filter, list_len, c] },
            }
        },
    }
}
