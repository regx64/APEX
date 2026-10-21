// A small body of verified elementary number theory ("Mathlib-lite": a few hundred lines,
// nothing like Mathlib's breadth). Loaded when a program mentions one of its names.

fn dvd(a: Nat, b: Nat) -> Prop { exists(k: Nat) -> b = a * k }
fn is_even(n: Nat) -> Prop { dvd(2, n) }
fn is_odd(n: Nat) -> Prop { exists(k: Nat) -> n = 2 * k + 1 }

theorem dvd_refl(a: Nat): dvd(a, a) := by { exists 1; ring }
theorem dvd_zero(a: Nat): dvd(a, 0) := by { exists 0 }
theorem one_dvd(a: Nat): dvd(1, a) := by { exists a; ring }
theorem dvd_trans(a: Nat, b: Nat, c: Nat, h1: dvd(a, b), h2: dvd(b, c)): dvd(a, c) := by {
    obtain (k, hk) := h1;
    obtain (m, hm) := h2;
    exists k * m;
    rw [hm, hk]; try ring
}
theorem dvd_add(a: Nat, b: Nat, c: Nat, h1: dvd(a, b), h2: dvd(a, c)): dvd(a, b + c) := by {
    obtain (k, hk) := h1;
    obtain (m, hm) := h2;
    exists k + m;
    rw [hk, hm]; try ring
}
theorem dvd_mul_right(a: Nat, b: Nat): dvd(a, a * b) := by { exists b }
theorem dvd_mul_left(a: Nat, b: Nat): dvd(a, b * a) := by { exists b; ring }
theorem dvd_of_dvd_mul(a: Nat, b: Nat, c: Nat, h: dvd(a, b)): dvd(a, b * c) := by {
    obtain (k, hk) := h;
    exists k * c;
    rw [hk]; try ring
}
theorem even_or_odd(n: Nat): Or<is_even(n), is_odd(n)> := by {
    induction n with {
        zero => { left; exists 0 },
        succ(k, ih) => {
            cases ih with {
                inl(h) => { obtain (m, hm) := h; right; exists m; rw [hm]; try ring },
                inr(h) => { obtain (m, hm) := h; left; exists m + 1; rw [hm]; try ring },
            }
        },
    }
}
theorem even_add(a: Nat, b: Nat, h1: is_even(a), h2: is_even(b)): is_even(a + b) := dvd_add(2, a, b, h1, h2)
theorem even_mul_left(a: Nat, b: Nat, h: is_even(a)): is_even(a * b) := dvd_of_dvd_mul(2, a, b, h)

// ---- sums and Gauss ----
fn sum_to(n: Nat) -> Nat { match n { 0 => 0, Nat.succ(k) => sum_to(k) + Nat.succ(k) } }
theorem gauss(n: Nat): 2 * sum_to(n) = n * (n + 1) := by {
    induction n with {
        zero => { rfl },
        succ(k, ih) => {
            have e: sum_to(Nat.succ(k)) = sum_to(k) + Nat.succ(k) := by { rfl };
            rw [e, mul_add, ih]; ring
        },
    }
}
fn sum_sq(n: Nat) -> Nat { match n { 0 => 0, Nat.succ(k) => sum_sq(k) + Nat.succ(k) * Nat.succ(k) } }
theorem sum_of_squares(n: Nat): 6 * sum_sq(n) = n * (n + 1) * (2 * n + 1) := by {
    induction n with {
        zero => { rfl },
        succ(k, ih) => {
            have e: sum_sq(Nat.succ(k)) = sum_sq(k) + Nat.succ(k) * Nat.succ(k) := by { rfl };
            rw [e, mul_add, ih]; ring
        },
    }
}

// ---- powers ----
theorem pow_succ_eq(b: Nat, e: Nat): nat_pow(b, Nat.succ(e)) = nat_pow(b, e) * b := by { rfl }
theorem pow_add(b: Nat, m: Nat, n: Nat): nat_pow(b, m + n) = nat_pow(b, m) * nat_pow(b, n) := by {
    induction n with {
        zero => { simp [nat_pow] },
        succ(k, ih) => { simp [nat_pow]; rw [ih]; ring },
    }
}
theorem two_pow_pos(n: Nat): lt(0, nat_pow(2, n)) := by {
    induction n with {
        zero => { simp [nat_pow]; omega },
        succ(k, ih) => { simp [nat_pow]; omega },
    }
}

// ---- Fibonacci ----
fn fib(n: Nat) -> Nat {
    match n { 0 => 0, 1 => 1, Nat.succ(Nat.succ(m)) => fib(m) + fib(Nat.succ(m)) }
}
theorem fib_pos(n: Nat): lt(0, fib(Nat.succ(n))) := by {
    induction n with {
        zero => { have e: fib(1) = 1 := by { rfl }; rw [e]; omega },
        succ(k, ih) => {
            have e: fib(Nat.succ(Nat.succ(k))) = fib(k) + fib(Nat.succ(k)) := by { rfl };
            rw [e]; omega
        },
    }
}
theorem fib_add_two(n: Nat): fib(n + 2) = fib(n) + fib(n + 1) := by { rfl }

// ---- primes ----
fn is_prime(p: Nat) -> Prop { And(le(2, p), forall(d: Nat) -> dvd(d, p) -> Or(d = 1, d = p)) }
theorem not_prime_one(h: is_prime(1)): False := by { obtain (h1, _) := h; omega }

theorem lt_two_pow(n: Nat): lt(n, nat_pow(2, n)) := by {
    induction n with {
        zero => { simp [nat_pow]; omega },
        succ(k, ih) => { simp [nat_pow]; omega },
    }
}
fn sum_odd(n: Nat) -> Nat { match n { 0 => 0, Nat.succ(k) => sum_odd(k) + (2 * k + 1) } }
theorem sum_of_odds(n: Nat): sum_odd(n) = n * n := by {
    induction n with {
        zero => { rfl },
        succ(k, ih) => {
            have e: sum_odd(Nat.succ(k)) = sum_odd(k) + (2 * k + 1) := by { rfl };
            rw [e, ih]; ring
        },
    }
}
theorem square_even_of_even(n: Nat, h: is_even(n)): is_even(n * n) := dvd_of_dvd_mul(2, n, n, h)
theorem dvd_le(a: Nat, b: Nat, hb: lt(0, b), h: dvd(a, b)): le(a, b) := by {
    obtain (k, hk) := h;
    cases k with {
        zero => { simp at hk; omega },
        succ(m) => { rw [hk]; exists a * m; ring },
    }
}
theorem prime_two(): is_prime(2) := by {
    constructor;
    omega;
    intro d hd;
    have hle: le(d, 2) := dvd_le(d, 2, by { omega }, hd);
    obtain (k, hk) := hd;
    cases d with {
        zero => { simp at hk; exfalso; omega },
        succ(d1) => {
            cases d1 with {
                zero => { left; rfl },
                succ(d2) => { right; omega },
            }
        },
    }
}
