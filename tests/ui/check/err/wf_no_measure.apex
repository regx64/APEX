// expect: nor is it provably terminating
fn bad(n: Nat) -> Nat {
    bad(n + 1)
}
