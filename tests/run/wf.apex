// out: 55
// out: 6
// out: 5
fn sum_down(n: Nat) -> Nat {
    if n == 0 { 0 } else { n + sum_down(n - 1) }
}

fn gcd(a: Nat, b: Nat) -> Nat termination_by b decreasing_by {
    have h: lt(0, b) := by { omega };
    have r: lt(nat_rem(a, b), b) := rem_lt(a, b, h);
    omega
} {
    if b == 0 { a } else { gcd(b, a % b) }
}

fn count_up(i: Nat, limit: Nat) -> Nat termination_by limit - i {
    if i < limit { 1 + count_up(i + 1, limit) } else { 0 }
}

fn main() -> IO<Unit> {
    do {
        println(Nat.toString(sum_down(10)));
        println(Nat.toString(gcd(48, 18)));
        println(Nat.toString(count_up(2, 7)))
    }
}
