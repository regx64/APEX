// out: 12
// out: 7
// A user function may reuse a prelude name; later code sees the user's one.
fn range(n: Nat) -> Nat { n * 4 }
fn list_len(n: Nat) -> Nat { n + 1 }

fn uses_them() -> Nat { range(3) }

fn main() -> IO<Unit> {
    do {
        display(uses_them());
        // the prelude's own functions are unaffected by the shadowing
        display(list_sum(list_map([1, 2, 3], |x| x + 1)) - 2);
    }
}
