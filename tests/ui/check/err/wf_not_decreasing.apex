// expect: decreases the measure
fn bad(n: Nat) -> Nat termination_by n {
    if n == 0 { 0 } else { bad(n + 1) }
}
