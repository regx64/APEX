// Standard-library data structures, written in APEX itself (loaded when mentioned):
// `Array` (a list with indexed access), `Map` (an association list) and a few `Nat` functions.

fn nat_pow(b: Nat, e: Nat) -> Nat { match e { 0 => 1, Nat.succ(k) => nat_pow(b, k) * b } }
fn nat_min(a: Nat, b: Nat) -> Nat { if nat_lt(a, b) { a } else { b } }
fn nat_max(a: Nat, b: Nat) -> Nat { if nat_lt(a, b) { b } else { a } }
/// Euclid's algorithm with the second argument as fuel-free measure (well-founded on `b`).
fn nat_gcd(a: Nat, b: Nat) -> Nat termination_by b decreasing_by { have h: lt(0, b) := by { omega }; rw [<- _hm]; exact rem_lt(a, b, h) } {
    if nat_beq(b, 0) { a } else { nat_gcd(b, nat_rem(a, b)) }
}

struct Array<T> { items: List<T> }

fn array_empty<T>() -> Array<T> { Array.mk(List.nil) }
fn array_size<T>(a: Array<T>) -> Nat { list_len(a.items) }
fn array_push<T>(a: Array<T>, x: T) -> Array<T> { Array.mk(list_append(a.items, List.cons(x, List.nil))) }
fn list_get<T>(xs: List<T>, i: Nat) -> Option<T> {
    match xs {
        List.nil => Option.None,
        List.cons(x, rest) => match i { 0 => Option.Some(x), Nat.succ(j) => list_get(rest, j) },
    }
}
fn array_get<T>(a: Array<T>, i: Nat) -> Option<T> { list_get(a.items, i) }
fn list_set<T>(xs: List<T>, i: Nat, v: T) -> List<T> {
    match xs {
        List.nil => List.nil,
        List.cons(x, rest) => match i { 0 => List.cons(v, rest), Nat.succ(j) => List.cons(x, list_set(rest, j, v)) },
    }
}
fn array_set<T>(a: Array<T>, i: Nat, v: T) -> Array<T> { Array.mk(list_set(a.items, i, v)) }
fn array_of_list<T>(xs: List<T>) -> Array<T> { Array.mk(xs) }

theorem list_get_nil<T>(xs: List<T>, i: Nat, h: xs = List.nil): list_get(xs, i) = Option.None := by {
    subst h; cases i with { zero => { rfl }, succ(k) => { rfl } }
}
theorem list_set_len<T>(xs: List<T>, i: Nat, v: T): list_len(list_set(xs, i, v)) = list_len(xs) := by {
    induction xs generalizing i with {
        nil => { rfl },
        cons(x, rest, ih) => {
            cases i with {
                zero => { rfl },
                succ(j) => { simp [list_set, list_len]; rw [ih(j)] },
            }
        },
    }
}

/// A finite map as an association list: the newest binding of a key wins.
struct Map<K, V> { entries: List<Prod<K, V>> }

fn map_empty<K, V>() -> Map<K, V> { Map.mk(List.nil) }
fn map_insert<K, V>(m: Map<K, V>, k: K, v: V) -> Map<K, V> { Map.mk(List.cons(Prod.mk(k, v), m.entries)) }
fn assoc_find<K: BEq, V>(es: List<Prod<K, V>>, k: K) -> Option<V> {
    match es {
        List.nil => Option.None,
        List.cons(e, rest) => if Prod.fst(e) == k { Option.Some(Prod.snd(e)) } else { assoc_find(rest, k) },
    }
}
fn map_get<K: BEq, V>(m: Map<K, V>, k: K) -> Option<V> { assoc_find(m.entries, k) }
fn map_size<K, V>(m: Map<K, V>) -> Nat { list_len(m.entries) }

