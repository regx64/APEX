// Well-founded recursion: the measure must decrease, proved by `decreasing_by` (default `omega`)

// no annotation: not structural (`n - 1` is not a subterm), so `n` is tried as the measure
fn sum_down(n: Nat) -> Nat {
    if n == 0 { 0 } else { n + sum_down(n - 1) }
}

// two parameters; the measure is the distance
fn count_up(i: Nat, limit: Nat) -> Nat termination_by limit - i {
    if i < limit { 1 + count_up(i + 1, limit) } else { 0 }
}

// a user lemma in `decreasing_by`
fn gcd(a: Nat, b: Nat) -> Nat termination_by b decreasing_by {
    have h: lt(0, b) := by { omega };
    have r: lt(nat_rem(a, b), b) := rem_lt(a, b, h);
    omega
} {
    if b == 0 { a } else { gcd(b, a % b) }
}

// the unfolding equations (`f.eq`) are what proofs about these functions use
theorem sum_down_zero(): sum_down(0) = 0 := by { rw [sum_down.eq] }
theorem gcd_zero(a: Nat): gcd(a, 0) = a := by { rw [gcd.eq] }
theorem gcd_step(a: Nat, b: Nat, h: lt(0, b)): gcd(a, b) = gcd(b, a % b) := by {
    rw [gcd.eq];
    have c: nat_beq(b, 0) = false := beq_of_pos(b, h);
    rw [c]
}
