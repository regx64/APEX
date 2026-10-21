// `Int`: integers as `ofNat n | negSucc n` (the value `-(n+1)`), as in Lean.
//
// The laws are proved through *representations*: `int_rep z p q` says `z = p - q` for natural
// numbers `p`, `q`. Every integer has one (`int_exists_rep`), the operations act on pairs
// (`int_add_rep`, `int_neg_rep`, `int_mul_rep`), and two integers whose pairs agree are equal
// (`int_eq_by_cross`). So each ring law reduces to a `Nat` identity, closed by `ring`/`omega`.
// The `omega` and `ring` tactics use the same translation for integer goals.

enum Int { ofNat(Nat), negSucc(Nat) }

fn int_sub_nat_nat(m: Nat, n: Nat) -> Int {
    match nat_sub(n, m) {
        0 => Int.ofNat(nat_sub(m, n)),
        Nat.succ(k) => Int.negSucc(k),
    }
}
fn int_neg_of_nat(n: Nat) -> Int {
    match n { 0 => Int.ofNat(0), Nat.succ(k) => Int.negSucc(k) }
}
fn int_neg(a: Int) -> Int {
    match a { Int.ofNat(n) => int_neg_of_nat(n), Int.negSucc(n) => Int.ofNat(Nat.succ(n)) }
}
fn int_add(a: Int, b: Int) -> Int {
    match a {
        Int.ofNat(m) => match b {
            Int.ofNat(n) => Int.ofNat(m + n),
            Int.negSucc(n) => int_sub_nat_nat(m, Nat.succ(n)),
        },
        Int.negSucc(m) => match b {
            Int.ofNat(n) => int_sub_nat_nat(n, Nat.succ(m)),
            Int.negSucc(n) => Int.negSucc(Nat.succ(m + n)),
        },
    }
}
fn int_sub(a: Int, b: Int) -> Int { int_add(a, int_neg(b)) }
fn int_mul(a: Int, b: Int) -> Int {
    match a {
        Int.ofNat(m) => match b {
            Int.ofNat(n) => Int.ofNat(m * n),
            Int.negSucc(n) => int_neg_of_nat(m * Nat.succ(n)),
        },
        Int.negSucc(m) => match b {
            Int.ofNat(n) => int_neg_of_nat(Nat.succ(m) * n),
            Int.negSucc(n) => Int.ofNat(Nat.succ(m) * Nat.succ(n)),
        },
    }
}
impl Add for Int { fn add(self, other: Self) -> Self { int_add(self, other) } }
impl Sub for Int { fn sub(self, other: Self) -> Self { int_sub(self, other) } }
impl Mul for Int { fn mul(self, other: Self) -> Self { int_mul(self, other) } }
impl Neg for Int { fn neg(self) -> Self { int_neg(self) } }
impl Coe<Int> for Nat { fn coe(self) -> Int { Int.ofNat(self) } }
fn int_beq(a: Int, b: Int) -> Bool {
    match a {
        Int.ofNat(m) => match b { Int.ofNat(n) => nat_beq(m, n), Int.negSucc(_) => false },
        Int.negSucc(m) => match b { Int.ofNat(_) => false, Int.negSucc(n) => nat_beq(m, n) },
    }
}
fn int_blt(a: Int, b: Int) -> Bool {
    match a {
        Int.ofNat(m) => match b { Int.ofNat(n) => nat_lt(m, n), Int.negSucc(_) => false },
        Int.negSucc(m) => match b { Int.ofNat(_) => true, Int.negSucc(n) => nat_lt(n, m) },
    }
}
impl BEq for Int { fn beq(self, other: Self) -> Bool { int_beq(self, other) } }
impl Ord for Int { fn lt(self, other: Self) -> Bool { int_blt(self, other) } }
impl Show for Int {
    fn show(&self) -> String {
        match self {
            Int.ofNat(n) => Nat.toString(n),
            Int.negSucc(n) => String.append("-", Nat.toString(Nat.succ(n))),
        }
    }
}
fn int_rep(z: Int, p: Nat, q: Nat) -> Prop {
    match z { Int.ofNat(n) => n + q = p, Int.negSucc(n) => p + Nat.succ(n) = q }
}
theorem int_rep_unique(z: Int, w: Int, p: Nat, q: Nat, h1: int_rep(z, p, q), h2: int_rep(w, p, q)): z = w := by {
    cases z with {
        ofNat(n) => {
            cases w with {
                ofNat(k) => {
                    simp [int_rep] at h1; simp [int_rep] at h2;
                    have e: n = k := by { omega };
                    rw [e]
                },
                negSucc(k) => { simp [int_rep] at h1; simp [int_rep] at h2; exfalso; omega },
            }
        },
        negSucc(n) => {
            cases w with {
                ofNat(k) => { simp [int_rep] at h1; simp [int_rep] at h2; exfalso; omega },
                negSucc(k) => {
                    simp [int_rep] at h1; simp [int_rep] at h2;
                    have e: n = k := by { omega };
                    rw [e]
                },
            }
        },
    }
}
theorem int_exists_rep(z: Int): exists(p: Nat) -> exists(q: Nat) -> int_rep(z, p, q) := by {
    cases z with {
        ofNat(n) => { exists n; exists 0 },
        negSucc(n) => { exists 0; exists Nat.succ(n); simp [int_rep] },
    }
}
theorem int_sub_nat_nat_rep(m: Nat, n: Nat, k: Nat): int_rep(int_sub_nat_nat(m, n), m + k, n + k) := by {
    simp [int_sub_nat_nat];
    cases hc : nat_sub(n, m) with {
        zero => { simp [int_rep]; omega },
        succ(j) => { simp [int_rep]; omega },
    }
}
theorem int_rep_congr(z: Int, p: Nat, q: Nat, p2: Nat, q2: Nat, hp: p = p2, hq: q = q2, h: int_rep(z, p, q)): int_rep(z, p2, q2) := by {
    subst hp; subst hq; exact h
}
theorem int_add_rep(a: Int, b: Int, p: Nat, q: Nat, r: Nat, s: Nat, h1: int_rep(a, p, q), h2: int_rep(b, r, s)):
        int_rep(int_add(a, b), p + r, q + s) := by {
    cases a with {
        ofNat(m) => {
            cases b with {
                ofNat(n) => { simp [int_add]; simp [int_rep] at h1; simp [int_rep] at h2; simp [int_rep]; omega },
                negSucc(n) => {
                    simp [int_add]; simp [int_rep] at h1; simp [int_rep] at h2;
                    exact int_rep_congr(int_sub_nat_nat(m, Nat.succ(n)), m + (q + r), Nat.succ(n) + (q + r), p + r, q + s,
                        by { omega }, by { omega }, int_sub_nat_nat_rep(m, Nat.succ(n), q + r))
                },
            }
        },
        negSucc(m) => {
            cases b with {
                ofNat(n) => {
                    simp [int_add]; simp [int_rep] at h1; simp [int_rep] at h2;
                    exact int_rep_congr(int_sub_nat_nat(n, Nat.succ(m)), n + (p + s), Nat.succ(m) + (p + s), p + r, q + s,
                        by { omega }, by { omega }, int_sub_nat_nat_rep(n, Nat.succ(m), p + s))
                },
                negSucc(n) => { simp [int_add]; simp [int_rep] at h1; simp [int_rep] at h2; simp [int_rep]; omega },
            }
        },
    }
}
theorem int_neg_of_nat_rep(k: Nat, p: Nat, q: Nat, h: p + k = q): int_rep(int_neg_of_nat(k), p, q) := by {
    cases k with {
        zero => { simp [int_neg_of_nat, int_rep]; omega },
        succ(j) => { simp [int_neg_of_nat, int_rep]; try omega },
    }
}
theorem int_neg_rep(a: Int, p: Nat, q: Nat, h: int_rep(a, p, q)): int_rep(int_neg(a), q, p) := by {
    cases a with {
        ofNat(n) => {
            simp [int_neg]; simp [int_rep] at h;
            exact int_neg_of_nat_rep(n, q, p, by { omega })
        },
        negSucc(n) => { simp [int_neg]; simp [int_rep] at h; simp [int_rep]; omega },
    }
}
theorem int_mul_rep(a: Int, b: Int, p: Nat, q: Nat, r: Nat, s: Nat, h1: int_rep(a, p, q), h2: int_rep(b, r, s)):
        int_rep(int_mul(a, b), p * r + q * s, p * s + q * r) := by {
    cases a with {
        ofNat(m) => {
            cases b with {
                ofNat(n) => {
                    simp [int_mul]; simp [int_rep] at h1; simp [int_rep] at h2; simp [int_rep];
                    subst h1; subst h2; ring
                },
                negSucc(n) => {
                    simp [int_mul]; simp [int_rep] at h1; simp [int_rep] at h2;
                    subst h1; subst h2;
                    apply int_neg_of_nat_rep; ring
                },
            }
        },
        negSucc(m) => {
            cases b with {
                ofNat(n) => {
                    simp [int_mul]; simp [int_rep] at h1; simp [int_rep] at h2;
                    subst h1; subst h2;
                    apply int_neg_of_nat_rep; ring
                },
                negSucc(n) => {
                    simp [int_mul]; simp [int_rep] at h1; simp [int_rep] at h2; simp [int_rep];
                    subst h1; subst h2; ring
                },
            }
        },
    }
}
theorem int_eq_by_reps(x: Int, y: Int, p: Nat, q: Nat, p2: Nat, q2: Nat, hx: int_rep(x, p, q), hy: int_rep(y, p2, q2), e1: p = p2, e2: q = q2): x = y := by {
    exact int_rep_unique(x, y, p2, q2, int_rep_congr(x, p, q, p2, q2, e1, e2, hx), hy)
}
theorem int_rep_shift(z: Int, p: Nat, q: Nat, k: Nat, h: int_rep(z, p, q)): int_rep(z, p + k, q + k) := by {
    cases z with {
        ofNat(n) => { simp [int_rep] at h; simp [int_rep]; omega },
        negSucc(n) => { simp [int_rep] at h; simp [int_rep]; omega },
    }
}
/// Two integers with representations `p - q` and `p2 - q2` are equal when `p + q2 = p2 + q`.
theorem int_eq_by_cross(x: Int, y: Int, p: Nat, q: Nat, p2: Nat, q2: Nat, hx: int_rep(x, p, q), hy: int_rep(y, p2, q2), e: p + q2 = p2 + q): x = y := by {
    exact int_eq_by_reps(x, y, p + q2, q + q2, p2 + q, q2 + q,
        int_rep_shift(x, p, q, q2, hx), int_rep_shift(y, p2, q2, q, hy), e, by { omega })
}
theorem int_add_comm(a: Int, b: Int): int_add(a, b) = int_add(b, a) := by {
    obtain (p, q, hp) := int_exists_rep(a);
    obtain (r, s, hr) := int_exists_rep(b);
    exact int_eq_by_reps(int_add(a, b), int_add(b, a), p + r, q + s, r + p, s + q,
        int_add_rep(a, b, p, q, r, s, hp, hr), int_add_rep(b, a, r, s, p, q, hr, hp), by { ring }, by { ring })
}
theorem int_add_assoc(a: Int, b: Int, c: Int): int_add(int_add(a, b), c) = int_add(a, int_add(b, c)) := by {
    obtain (p, q, hp) := int_exists_rep(a);
    obtain (r, s, hr) := int_exists_rep(b);
    obtain (u, v, hu) := int_exists_rep(c);
    exact int_eq_by_reps(int_add(int_add(a, b), c), int_add(a, int_add(b, c)), (p + r) + u, (q + s) + v, p + (r + u), q + (s + v),
        int_add_rep(int_add(a, b), c, p + r, q + s, u, v, int_add_rep(a, b, p, q, r, s, hp, hr), hu),
        int_add_rep(a, int_add(b, c), p, q, r + u, s + v, hp, int_add_rep(b, c, r, s, u, v, hr, hu)),
        by { ring }, by { ring })
}
theorem int_zero_rep(): int_rep(Int.ofNat(0), 0, 0) := by { simp [int_rep] }
theorem int_one_rep(): int_rep(Int.ofNat(1), 1, 0) := by { simp [int_rep] }
theorem int_add_zero(a: Int): int_add(a, Int.ofNat(0)) = a := by {
    obtain (p, q, hp) := int_exists_rep(a);
    exact int_eq_by_reps(int_add(a, Int.ofNat(0)), a, p + 0, q + 0, p, q,
        int_add_rep(a, Int.ofNat(0), p, q, 0, 0, hp, int_zero_rep()), hp, by { ring }, by { ring })
}
theorem int_zero_add(a: Int): int_add(Int.ofNat(0), a) = a := by {
    rw [int_add_comm]; exact int_add_zero(a)
}
theorem int_add_neg_cancel(a: Int): int_add(a, int_neg(a)) = Int.ofNat(0) := by {
    obtain (p, q, hp) := int_exists_rep(a);
    exact int_eq_by_cross(int_add(a, int_neg(a)), Int.ofNat(0), p + q, q + p, 0, 0,
        int_add_rep(a, int_neg(a), p, q, q, p, hp, int_neg_rep(a, p, q, hp)), int_zero_rep(), by { ring })
}
theorem int_neg_neg(a: Int): int_neg(int_neg(a)) = a := by {
    obtain (p, q, hp) := int_exists_rep(a);
    exact int_rep_unique(int_neg(int_neg(a)), a, p, q, int_neg_rep(int_neg(a), q, p, int_neg_rep(a, p, q, hp)), hp)
}
theorem int_mul_comm(a: Int, b: Int): int_mul(a, b) = int_mul(b, a) := by {
    obtain (p, q, hp) := int_exists_rep(a);
    obtain (r, s, hr) := int_exists_rep(b);
    exact int_eq_by_reps(int_mul(a, b), int_mul(b, a), p * r + q * s, p * s + q * r, r * p + s * q, r * q + s * p,
        int_mul_rep(a, b, p, q, r, s, hp, hr), int_mul_rep(b, a, r, s, p, q, hr, hp), by { ring }, by { ring })
}
theorem int_mul_assoc(a: Int, b: Int, c: Int): int_mul(int_mul(a, b), c) = int_mul(a, int_mul(b, c)) := by {
    obtain (p, q, hp) := int_exists_rep(a);
    obtain (r, s, hr) := int_exists_rep(b);
    obtain (u, v, hu) := int_exists_rep(c);
    exact int_eq_by_reps(int_mul(int_mul(a, b), c), int_mul(a, int_mul(b, c)),
        (p * r + q * s) * u + (p * s + q * r) * v, (p * r + q * s) * v + (p * s + q * r) * u,
        p * (r * u + s * v) + q * (r * v + s * u), p * (r * v + s * u) + q * (r * u + s * v),
        int_mul_rep(int_mul(a, b), c, p * r + q * s, p * s + q * r, u, v, int_mul_rep(a, b, p, q, r, s, hp, hr), hu),
        int_mul_rep(a, int_mul(b, c), p, q, r * u + s * v, r * v + s * u, hp, int_mul_rep(b, c, r, s, u, v, hr, hu)),
        by { ring }, by { ring })
}
theorem int_mul_one(a: Int): int_mul(a, Int.ofNat(1)) = a := by {
    obtain (p, q, hp) := int_exists_rep(a);
    exact int_eq_by_reps(int_mul(a, Int.ofNat(1)), a, p * 1 + q * 0, p * 0 + q * 1, p, q,
        int_mul_rep(a, Int.ofNat(1), p, q, 1, 0, hp, int_one_rep()), hp, by { ring }, by { ring })
}
theorem int_one_mul(a: Int): int_mul(Int.ofNat(1), a) = a := by { rw [int_mul_comm]; exact int_mul_one(a) }
theorem int_mul_zero(a: Int): int_mul(a, Int.ofNat(0)) = Int.ofNat(0) := by {
    obtain (p, q, hp) := int_exists_rep(a);
    exact int_eq_by_reps(int_mul(a, Int.ofNat(0)), Int.ofNat(0), p * 0 + q * 0, p * 0 + q * 0, 0, 0,
        int_mul_rep(a, Int.ofNat(0), p, q, 0, 0, hp, int_zero_rep()), int_zero_rep(), by { ring }, by { ring })
}
theorem int_zero_mul(a: Int): int_mul(Int.ofNat(0), a) = Int.ofNat(0) := by { rw [int_mul_comm]; exact int_mul_zero(a) }
theorem int_mul_add(a: Int, b: Int, c: Int): int_mul(a, int_add(b, c)) = int_add(int_mul(a, b), int_mul(a, c)) := by {
    obtain (p, q, hp) := int_exists_rep(a);
    obtain (r, s, hr) := int_exists_rep(b);
    obtain (u, v, hu) := int_exists_rep(c);
    exact int_eq_by_reps(int_mul(a, int_add(b, c)), int_add(int_mul(a, b), int_mul(a, c)),
        p * (r + u) + q * (s + v), p * (s + v) + q * (r + u),
        (p * r + q * s) + (p * u + q * v), (p * s + q * r) + (p * v + q * u),
        int_mul_rep(a, int_add(b, c), p, q, r + u, s + v, hp, int_add_rep(b, c, r, s, u, v, hr, hu)),
        int_add_rep(int_mul(a, b), int_mul(a, c), p * r + q * s, p * s + q * r, p * u + q * v, p * v + q * u,
            int_mul_rep(a, b, p, q, r, s, hp, hr), int_mul_rep(a, c, p, q, u, v, hp, hu)),
        by { ring }, by { ring })
}
theorem int_add_mul(a: Int, b: Int, c: Int): int_mul(int_add(a, b), c) = int_add(int_mul(a, c), int_mul(b, c)) := by {
    rw [int_mul_comm, int_mul_add, int_mul_comm(c, a), int_mul_comm(c, b)]
}
theorem int_sub_self(a: Int): int_sub(a, a) = Int.ofNat(0) := by { exact int_add_neg_cancel(a) }
fn int_le(a: Int, b: Int) -> Prop { exists(n: Nat) -> int_add(a, Int.ofNat(n)) = b }
fn int_lt(a: Int, b: Int) -> Prop { int_le(int_add(a, Int.ofNat(1)), b) }
theorem int_le_of_rep(a: Int, b: Int, p: Nat, q: Nat, r: Nat, s: Nat, ha: int_rep(a, p, q), hb: int_rep(b, r, s), h: le(p + s, r + q)): int_le(a, b) := by {
    obtain (k, hk) := h;
    exists k;
    exact int_eq_by_cross(int_add(a, Int.ofNat(k)), b, p + k, q + 0, r, s,
        int_add_rep(a, Int.ofNat(k), p, q, k, 0, ha, by { simp [int_rep] }), hb, by { omega })
}
theorem int_rep_cross(z: Int, p: Nat, q: Nat, r: Nat, s: Nat, h1: int_rep(z, p, q), h2: int_rep(z, r, s)): p + s = r + q := by {
    cases z with {
        ofNat(n) => { simp [int_rep] at h1; simp [int_rep] at h2; omega },
        negSucc(n) => { simp [int_rep] at h1; simp [int_rep] at h2; omega },
    }
}
theorem int_rep_of_le(a: Int, b: Int, p: Nat, q: Nat, r: Nat, s: Nat, ha: int_rep(a, p, q), hb: int_rep(b, r, s), h: int_le(a, b)): le(p + s, r + q) := by {
    obtain (k, hk) := h;
    have h1: int_rep(int_add(a, Int.ofNat(k)), p + k, q + 0) := int_add_rep(a, Int.ofNat(k), p, q, k, 0, ha, by { simp [int_rep] });
    rw [hk] at h1;
    have e: (p + k) + s = r + (q + 0) := int_rep_cross(b, p + k, q + 0, r, s, h1, hb);
    exists k;
    omega
}

theorem int_ofNat_rep(n: Nat): int_rep(Int.ofNat(n), n, 0) := by { simp [int_rep] }
theorem int_eq_cross(a: Int, b: Int, p: Nat, q: Nat, r: Nat, s: Nat, ha: int_rep(a, p, q), hb: int_rep(b, r, s), h: a = b): p + s = r + q := by {
    subst h; exact int_rep_cross(a, p, q, r, s, ha, hb)
}
theorem int_ne_cross(a: Int, b: Int, p: Nat, q: Nat, r: Nat, s: Nat, ha: int_rep(a, p, q), hb: int_rep(b, r, s), h: Not<a = b>): Not<p + s = r + q> := by {
    intro e;
    exact h(int_eq_by_cross(a, b, p, q, r, s, ha, hb, e))
}
theorem int_negSucc_rep(n: Nat): int_rep(Int.negSucc(n), 0, Nat.succ(n)) := by { simp [int_rep] }
theorem int_lt_of_rep(a: Int, b: Int, p: Nat, q: Nat, r: Nat, s: Nat, ha: int_rep(a, p, q), hb: int_rep(b, r, s), h: lt(p + s, r + q)): int_lt(a, b) := by {
    exact int_le_of_rep(int_add(a, Int.ofNat(1)), b, p + 1, q + 0, r, s,
        int_add_rep(a, Int.ofNat(1), p, q, 1, 0, ha, int_one_rep()), hb, by { omega })
}
theorem int_rep_of_lt(a: Int, b: Int, p: Nat, q: Nat, r: Nat, s: Nat, ha: int_rep(a, p, q), hb: int_rep(b, r, s), h: int_lt(a, b)): lt(p + s, r + q) := by {
    have x: le(p + 1 + s, r + (q + 0)) := int_rep_of_le(int_add(a, Int.ofNat(1)), b, p + 1, q + 0, r, s,
        int_add_rep(a, Int.ofNat(1), p, q, 1, 0, ha, int_one_rep()), hb, h);
    omega
}
theorem int_not_le_cross(a: Int, b: Int, p: Nat, q: Nat, r: Nat, s: Nat, ha: int_rep(a, p, q), hb: int_rep(b, r, s), h: Not<int_le(a, b)>): Not<le(p + s, r + q)> := by {
    intro x;
    exact h(int_le_of_rep(a, b, p, q, r, s, ha, hb, x))
}
theorem int_not_lt_cross(a: Int, b: Int, p: Nat, q: Nat, r: Nat, s: Nat, ha: int_rep(a, p, q), hb: int_rep(b, r, s), h: Not<int_lt(a, b)>): Not<lt(p + s, r + q)> := by {
    intro x;
    exact h(int_lt_of_rep(a, b, p, q, r, s, ha, hb, x))
}
impl LE for Int { fn le(self, other: Self) -> Prop { int_le(self, other) } }
theorem int_le_refl(a: Int): int_le(a, a) := by { exists 0; exact int_add_zero(a) }
theorem int_le_trans(a: Int, b: Int, c: Int, h1: int_le(a, b), h2: int_le(b, c)): int_le(a, c) := by {
    obtain (p, q, hp) := int_exists_rep(a);
    obtain (r, s, hr) := int_exists_rep(b);
    obtain (u, v, hu) := int_exists_rep(c);
    exact int_le_of_rep(a, c, p, q, u, v, hp, hu, by {
        have x1: le(p + s, r + q) := int_rep_of_le(a, b, p, q, r, s, hp, hr, h1);
        have x2: le(r + v, u + s) := int_rep_of_le(b, c, r, s, u, v, hr, hu, h2);
        omega })
}
theorem int_le_antisymm(a: Int, b: Int, h1: int_le(a, b), h2: int_le(b, a)): a = b := by {
    obtain (p, q, hp) := int_exists_rep(a);
    obtain (r, s, hr) := int_exists_rep(b);
    exact int_eq_by_cross(a, b, p, q, r, s, hp, hr, by {
        have x1: le(p + s, r + q) := int_rep_of_le(a, b, p, q, r, s, hp, hr, h1);
        have x2: le(r + q, p + s) := int_rep_of_le(b, a, r, s, p, q, hr, hp, h2);
        omega })
}
theorem int_le_total(a: Int, b: Int): Or<int_le(a, b), int_le(b, a)> := by {
    obtain (p, q, hp) := int_exists_rep(a);
    obtain (r, s, hr) := int_exists_rep(b);
    cases le_or_lt(p + s, r + q) with {
        inl(h) => { left; exact int_le_of_rep(a, b, p, q, r, s, hp, hr, h) },
        inr(h) => { right; exact int_le_of_rep(b, a, r, s, p, q, hr, hp, by { omega }) },
    }
}
theorem int_add_le_add(a: Int, b: Int, c: Int, d: Int, h1: int_le(a, b), h2: int_le(c, d)): int_le(int_add(a, c), int_add(b, d)) := by {
    obtain (p, q, hp) := int_exists_rep(a);
    obtain (r, s, hr) := int_exists_rep(b);
    obtain (u, v, hu) := int_exists_rep(c);
    obtain (x, y, hx) := int_exists_rep(d);
    exact int_le_of_rep(int_add(a, c), int_add(b, d), p + u, q + v, r + x, s + y,
        int_add_rep(a, c, p, q, u, v, hp, hu), int_add_rep(b, d, r, s, x, y, hr, hx), by {
        have x1: le(p + s, r + q) := int_rep_of_le(a, b, p, q, r, s, hp, hr, h1);
        have x2: le(u + y, x + v) := int_rep_of_le(c, d, u, v, x, y, hu, hx, h2);
        omega })
}
