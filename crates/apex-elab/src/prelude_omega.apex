// Verified linear-arithmetic machinery behind the `omega` tactic: Nat order, a reflected
// linear-expression language, and a checker for Farkas-style certificates (omega_sound).

theorem add_left_comm(a: Nat, b: Nat, c: Nat): a + (b + c) = b + (a + c) := by {
    rw [<- add_assoc, add_comm(a, b), add_assoc]
}
theorem add_right_comm(a: Nat, b: Nat, c: Nat): (a + b) + c = (a + c) + b := by {
    rw [add_assoc, add_comm(b, c), <- add_assoc]
}
theorem add_add_add_comm(a: Nat, b: Nat, c: Nat, d: Nat): (a + b) + (c + d) = (a + c) + (b + d) := by {
    rw [add_assoc, <- add_assoc(b, c, d), add_comm(b, c), add_assoc(c, b, d), <- add_assoc]
}
theorem succ_inj(a: Nat, b: Nat, h: Nat.succ(a) = Nat.succ(b)): a = b := by {
    exact congr_arg(nat_pred, h)
}
theorem add_left_cancel(a: Nat, b: Nat, c: Nat): a + b = a + c -> b = c := by {
    induction a with {
        zero => { intro h; simp at h; exact h },
        succ(k, ih) => { intro h; simp at h; exact ih(succ_inj(k + b, k + c, h)) },
    }
}
theorem add_right_cancel(a: Nat, b: Nat, c: Nat, h: a + c = b + c): a = b := by {
    rw [add_comm(a, c), add_comm(b, c)] at h;
    exact add_left_cancel(c, a, b, h)
}
fn le(a: Nat, b: Nat) -> Prop { Exists(|k: Nat| a + k = b) }
fn lt(a: Nat, b: Nat) -> Prop { le(Nat.succ(a), b) }

fn bool_is_true(b: Bool) -> Prop { match b { true => True, false => False } }
fn nat_is_succ_p(n: Nat) -> Prop { match n { 0 => False, Nat.succ(_) => True } }

theorem false_ne_true(h: false = true): False := by {
    exact Eq.subst(bool_is_true, Eq.symm(h), True.intro)
}
theorem succ_ne_zero(n: Nat, h: Nat.succ(n) = 0): False := by {
    exact Eq.subst(nat_is_succ_p, h, True.intro)
}
theorem le_refl(a: Nat): le(a, a) := by { exists 0 }
theorem le_add_right(a: Nat, k: Nat): le(a, a + k) := by { exists k }
theorem le_trans(a: Nat, b: Nat, c: Nat, h1: le(a, b), h2: le(b, c)): le(a, c) := by {
    cases h1 with { intro(k, hk) => {
        cases h2 with { intro(m, hm) => {
            exists k + m;
            rw [<- add_assoc, hk, hm]
        } }
    } }
}
theorem add_le_add(a: Nat, b: Nat, c: Nat, d: Nat, h1: le(a, b), h2: le(c, d)): le(a + c, b + d) := by {
    cases h1 with { intro(k, hk) => {
        cases h2 with { intro(m, hm) => {
            exists k + m;
            rw [add_add_add_comm, hk, hm]
        } }
    } }
}
theorem mul_add(a: Nat, b: Nat, c: Nat): a * (b + c) = a * b + a * c := by {
    induction c with {
        zero => { rfl },
        succ(k, ih) => { simp [ih]; rw [add_assoc] },
    }
}
theorem mul_assoc(a: Nat, b: Nat, c: Nat): (a * b) * c = a * (b * c) := by {
    induction c with {
        zero => { rfl },
        succ(k, ih) => { simp [ih, mul_add] },
    }
}
theorem mul_le_mul_left(k: Nat, a: Nat, b: Nat, h: le(a, b)): le(k * a, k * b) := by {
    cases h with { intro(w, hw) => {
        exists k * w;
        rw [<- mul_add, hw]
    } }
}
theorem lt_irrefl(a: Nat, h: lt(a, a)): False := by {
    cases h with { intro(k, hk) => {
        have h2: a + Nat.succ(k) = a + 0 := by { simp; simp at hk; exact hk };
        exact succ_ne_zero(k, add_left_cancel(a, Nat.succ(k), 0, h2))
    } }
}
theorem add_mul(a: Nat, b: Nat, c: Nat): (a + b) * c = a * c + b * c := by {
    rw [mul_comm, mul_add, mul_comm(c, a), mul_comm(c, b)]
}
theorem add_eq_zero_left(a: Nat, b: Nat, h: a + b = 0): a = 0 := by {
    cases a with {
        zero => { rfl },
        succ(k) => { simp at h; exact False.elim(succ_ne_zero(k + b, h)) },
    }
}
theorem le_antisymm(a: Nat, b: Nat, h1: le(a, b), h2: le(b, a)): a = b := by {
    cases h1 with { intro(k, hk) => {
        cases h2 with { intro(m, hm) => {
            have h3: a + (k + m) = a + 0 := by { rw [<- add_assoc, hk, hm] };
            have h4: k = 0 := add_eq_zero_left(k, m, add_left_cancel(a, k + m, 0, h3));
            rw [h4] at hk;
            exact hk
        } }
    } }
}
theorem succ_le_succ(a: Nat, b: Nat, h: le(a, b)): le(Nat.succ(a), Nat.succ(b)) := by {
    cases h with { intro(k, hk) => { exists k; simp; rw [hk] } }
}
theorem zero_le(b: Nat): le(0, b) := by { exists b; simp }
theorem le_or_lt(a: Nat, b: Nat): Or<le(a, b), lt(b, a)> := by {
    induction a generalizing b with {
        zero => { left; exact zero_le(b) },
        succ(k, ih) => {
            cases b with {
                zero => { right; exists k; simp },
                succ(m) => {
                    cases ih(m) with {
                        inl(h) => { left; exact succ_le_succ(k, m, h) },
                        inr(h) => { right; exact succ_le_succ(Nat.succ(m), k, h) },
                    }
                },
            }
        },
    }
}
fn nat_ble(a: Nat, b: Nat) -> Bool {
    match a {
        0 => true,
        Nat.succ(x) => match b {
            0 => false,
            Nat.succ(y) => nat_ble(x, y),
        },
    }
}
theorem ble_sound(a: Nat, b: Nat): nat_ble(a, b) = true -> le(a, b) := by {
    induction a generalizing b with {
        zero => { intro h; exact zero_le(b) },
        succ(k, ih) => {
            cases b with {
                zero => { intro h; exact False.elim(false_ne_true(h)) },
                succ(m) => { intro h; exact succ_le_succ(k, m, ih(m, h)) },
            }
        },
    }
}
theorem lt_sound(a: Nat, b: Nat): nat_lt(a, b) = true -> lt(a, b) := by {
    induction a generalizing b with {
        zero => {
            cases b with {
                zero => { intro h; exact False.elim(false_ne_true(h)) },
                succ(m) => { intro h; exists m; simp },
            }
        },
        succ(k, ih) => {
            cases b with {
                zero => { intro h; exact False.elim(false_ne_true(h)) },
                succ(m) => { intro h; exact succ_le_succ(Nat.succ(k), m, ih(m, h)) },
            }
        },
    }
}
enum LExpr {
    Atom(Nat),
    Const(Nat),
    Add(LExpr, LExpr),
    Scale(Nat, LExpr),
    /// `e * c` (the literal on the right)
    ScaleR(LExpr, Nat),
}

fn lget(env: List<Nat>, i: Nat) -> Nat {
    match env {
        List.nil => 0,
        List.cons(x, rest) => match i {
            0 => x,
            Nat.succ(j) => lget(rest, j),
        },
    }
}

fn leval(e: LExpr, env: List<Nat>) -> Nat {
    match e {
        LExpr.Atom(i) => lget(env, i),
        LExpr.Const(c) => c,
        LExpr.Add(a, b) => leval(a, env) + leval(b, env),
        LExpr.Scale(c, x) => c * leval(x, env),
        LExpr.ScaleR(x, c) => leval(x, env) * c,
    }
}

fn dot(cs: List<Nat>, env: List<Nat>) -> Nat {
    match cs {
        List.nil => 0,
        List.cons(c, rest) => match env {
            List.nil => 0,
            List.cons(x, xs) => c * x + dot(rest, xs),
        },
    }
}

fn cadd(xs: List<Nat>, ys: List<Nat>) -> List<Nat> {
    match xs {
        List.nil => ys,
        List.cons(x, xr) => match ys {
            List.nil => xs,
            List.cons(y, yr) => List.cons(x + y, cadd(xr, yr)),
        },
    }
}

fn cscale(c: Nat, xs: List<Nat>) -> List<Nat> {
    match xs {
        List.nil => List.nil,
        List.cons(x, r) => List.cons(c * x, cscale(c, r)),
    }
}

fn cunit(i: Nat) -> List<Nat> {
    match i {
        0 => [1],
        Nat.succ(j) => List.cons(0, cunit(j)),
    }
}

fn cof(e: LExpr) -> List<Nat> {
    match e {
        LExpr.Atom(i) => cunit(i),
        LExpr.Const(c) => List.nil,
        LExpr.Add(a, b) => cadd(cof(a), cof(b)),
        LExpr.Scale(c, x) => cscale(c, cof(x)),
        LExpr.ScaleR(x, c) => cscale(c, cof(x)),
    }
}

fn kof(e: LExpr) -> Nat {
    match e {
        LExpr.Atom(i) => 0,
        LExpr.Const(c) => c,
        LExpr.Add(a, b) => kof(a) + kof(b),
        LExpr.Scale(c, x) => c * kof(x),
        LExpr.ScaleR(x, c) => kof(x) * c,
    }
}
theorem dot_cunit(i: Nat, env: List<Nat>): dot(cunit(i), env) = lget(env, i) := by {
    induction i generalizing env with {
        zero => {
            cases env with {
                nil => { rfl },
                cons(x, xs) => { simp },
            }
        },
        succ(j, ih) => {
            cases env with {
                nil => { rfl },
                cons(x, xs) => {
                    show 0 * x + dot(cunit(j), xs) = lget(xs, j);
                    simp [ih]
                },
            }
        },
    }
}
theorem dot_cadd(xs: List<Nat>, ys: List<Nat>, env: List<Nat>): dot(cadd(xs, ys), env) = dot(xs, env) + dot(ys, env) := by {
    induction xs generalizing ys env with {
        nil => { simp },
        cons(x, xr, ih) => {
            cases ys with {
                nil => { simp },
                cons(y, yr) => {
                    cases env with {
                        nil => { simp },
                        cons(e, es) => {
                            show (x + y) * e + dot(cadd(xr, yr), es) = (x * e + dot(xr, es)) + (y * e + dot(yr, es));
                            simp [ih, add_mul];
                            rw [add_add_add_comm]
                        },
                    }
                },
            }
        },
    }
}
theorem dot_cscale(c: Nat, xs: List<Nat>, env: List<Nat>): dot(cscale(c, xs), env) = c * dot(xs, env) := by {
    induction xs generalizing env with {
        nil => { simp },
        cons(x, xr, ih) => {
            cases env with {
                nil => { simp },
                cons(e, es) => {
                    show (c * x) * e + dot(cscale(c, xr), es) = c * (x * e + dot(xr, es));
                    simp [ih, mul_add, mul_assoc]
                },
            }
        },
    }
}
theorem lin_sound(e: LExpr, env: List<Nat>): leval(e, env) = dot(cof(e), env) + kof(e) := by {
    induction e with {
        Atom(i) => { simp [dot_cunit] },
        Const(c) => { simp },
        Add(a, b, iha, ihb) => {
            show leval(a, env) + leval(b, env) = dot(cadd(cof(a), cof(b)), env) + (kof(a) + kof(b));
            simp [dot_cadd, iha, ihb];
            rw [add_add_add_comm]
        },
        Scale(c, x, ih) => {
            show c * leval(x, env) = dot(cscale(c, cof(x)), env) + c * kof(x);
            simp [dot_cscale, ih, mul_add]
        },
        ScaleR(x, c, ih) => {
            show leval(x, env) * c = dot(cscale(c, cof(x)), env) + kof(x) * c;
            rw [ih, dot_cscale, add_mul, mul_comm(dot(cof(x), env), c)]
        },
    }
}
struct Cstr { lo: LExpr, hi: LExpr }

fn sum_lo(cs: List<Cstr>, ws: List<Nat>) -> LExpr {
    match cs {
        List.nil => LExpr.Const(0),
        List.cons(c, rest) => match ws {
            List.nil => LExpr.Const(0),
            List.cons(w, wr) => LExpr.Add(LExpr.Scale(w, c.lo), sum_lo(rest, wr)),
        },
    }
}
fn sum_hi(cs: List<Cstr>, ws: List<Nat>) -> LExpr {
    match cs {
        List.nil => LExpr.Const(0),
        List.cons(c, rest) => match ws {
            List.nil => LExpr.Const(0),
            List.cons(w, wr) => LExpr.Add(LExpr.Scale(w, c.hi), sum_hi(rest, wr)),
        },
    }
}
fn holds(cs: List<Cstr>, env: List<Nat>) -> Prop {
    match cs {
        List.nil => True,
        List.cons(c, rest) => And(le(leval(c.lo, env), leval(c.hi, env)), holds(rest, env)),
    }
}
theorem sum_sound(cs: List<Cstr>, ws: List<Nat>, env: List<Nat>, h: holds(cs, env)): le(leval(sum_lo(cs, ws), env), leval(sum_hi(cs, ws), env)) := by {
    induction cs generalizing ws with {
        nil => { simp; exact le_refl(0) },
        cons(c, rest, ih) => {
            cases ws with {
                nil => { simp; exact le_refl(0) },
                cons(w, wr) => {
                    cases h with { intro(h1, h2) => {
                        show le(w * leval(c.lo, env) + leval(sum_lo(rest, wr), env), w * leval(c.hi, env) + leval(sum_hi(rest, wr), env));
                        exact add_le_add(w * leval(c.lo, env), w * leval(c.hi, env), leval(sum_lo(rest, wr), env), leval(sum_hi(rest, wr), env), mul_le_mul_left(w, leval(c.lo, env), leval(c.hi, env), h1), ih(wr, h2))
                    } }
                },
            }
        },
    }
}
fn band(a: Bool, b: Bool) -> Bool { match a { true => b, false => false } }
theorem band_true(a: Bool, b: Bool, h: band(a, b) = true): And<a = true, b = true> := by {
    cases a with {
        false => { exact False.elim(false_ne_true(h)) },
        true => { constructor; rfl; exact h },
    }
}
theorem beq_sound(a: Nat, b: Nat): nat_beq(a, b) = true -> a = b := by {
    induction a generalizing b with {
        zero => {
            cases b with {
                zero => { intro h; rfl },
                succ(m) => { intro h; exact False.elim(false_ne_true(h)) },
            }
        },
        succ(k, ih) => {
            cases b with {
                zero => { intro h; exact False.elim(false_ne_true(h)) },
                succ(m) => { intro h; exact congr_arg(Nat.succ, ih(m, h)) },
            }
        },
    }
}
fn all_zero(ys: List<Nat>) -> Bool {
    match ys {
        List.nil => true,
        List.cons(y, yr) => band(nat_beq(y, 0), all_zero(yr)),
    }
}
theorem all_zero_dot(ys: List<Nat>, env: List<Nat>, h: all_zero(ys) = true): dot(ys, env) = 0 := by {
    induction ys generalizing env with {
        nil => { simp },
        cons(y, yr, ih) => {
            cases env with {
                nil => { simp },
                cons(e, es) => {
                    cases band_true(nat_beq(y, 0), all_zero(yr), h) with { intro(h1, h2) => {
                        show y * e + dot(yr, es) = 0;
                        rw [beq_sound(y, 0, h1), ih(es, h2)];
                        simp
                    } }
                },
            }
        },
    }
}
fn dominates(xs: List<Nat>, ys: List<Nat>) -> Bool {
    match xs {
        List.nil => all_zero(ys),
        List.cons(x, xr) => match ys {
            List.nil => true,
            List.cons(y, yr) => band(nat_ble(y, x), dominates(xr, yr)),
        },
    }
}
theorem mul_le_mul_right(k: Nat, a: Nat, b: Nat, h: le(a, b)): le(a * k, b * k) := by {
    rw [mul_comm(a, k), mul_comm(b, k)];
    exact mul_le_mul_left(k, a, b, h)
}
theorem dominates_sound(xs: List<Nat>, ys: List<Nat>, env: List<Nat>, h: dominates(xs, ys) = true): le(dot(ys, env), dot(xs, env)) := by {
    induction xs generalizing ys env with {
        nil => {
            rw [all_zero_dot(ys, env, h)];
            exact le_refl(0)
        },
        cons(x, xr, ih) => {
            cases ys with {
                nil => { simp; exact zero_le(dot(List.cons(x, xr), env)) },
                cons(y, yr) => {
                    cases env with {
                        nil => { simp; exact le_refl(0) },
                        cons(e, es) => {
                            cases band_true(nat_ble(y, x), dominates(xr, yr), h) with { intro(h1, h2) => {
                                show le(y * e + dot(yr, es), x * e + dot(xr, es));
                                exact add_le_add(y * e, x * e, dot(yr, es), dot(xr, es), mul_le_mul_right(e, y, x, ble_sound(y, x, h1)), ih(yr, es, h2))
                            } }
                        },
                    }
                },
            }
        },
    }
}
theorem le_add_cancel_left(a: Nat, b: Nat, c: Nat, h: le(a + b, a + c)): le(b, c) := by {
    cases h with { intro(k, hk) => {
        exists k;
        have h2: a + (b + k) = a + c := by { rw [<- add_assoc]; exact hk };
        exact add_left_cancel(a, b + k, c, h2)
    } }
}
theorem contra(dp: Nat, dq: Nat, kp: Nat, kq: Nat, s: le(dp + kp, dq + kq), dm: le(dq, dp), h: lt(kq, kp)): False := by {
    have t1: le(dq + kq, dp + kq) := add_le_add(dq, dp, kq, kq, dm, le_refl(kq));
    have t2: le(dp + kp, dp + kq) := le_trans(dp + kp, dq + kq, dp + kq, s, t1);
    have t3: le(kp, kq) := le_add_cancel_left(dp, kp, kq, t2);
    exact lt_irrefl(kq, le_trans(Nat.succ(kq), kp, kq, h, t3))
}
theorem omega_sound(cs: List<Cstr>, ws: List<Nat>, env: List<Nat>, h1: dominates(cof(sum_lo(cs, ws)), cof(sum_hi(cs, ws))) = true, h2: nat_lt(kof(sum_hi(cs, ws)), kof(sum_lo(cs, ws))) = true, h: holds(cs, env)): False := by {
    have s: le(leval(sum_lo(cs, ws), env), leval(sum_hi(cs, ws), env)) := sum_sound(cs, ws, env, h);
    rw [lin_sound(sum_lo(cs, ws), env), lin_sound(sum_hi(cs, ws), env)] at s;
    exact contra(dot(cof(sum_lo(cs, ws)), env), dot(cof(sum_hi(cs, ws)), env), kof(sum_lo(cs, ws)), kof(sum_hi(cs, ws)), s, dominates_sound(cof(sum_lo(cs, ws)), cof(sum_hi(cs, ws)), env, h1), lt_sound(kof(sum_hi(cs, ws)), kof(sum_lo(cs, ws)), h2))
}
theorem le_of_not_lt(a: Nat, b: Nat, h: Not<lt(b, a)>): le(a, b) := by {
    cases le_or_lt(a, b) with {
        inl(x) => { exact x },
        inr(x) => { exact False.elim(h(x)) },
    }
}
theorem lt_of_not_le(a: Nat, b: Nat, h: Not<le(a, b)>): lt(b, a) := by {
    cases le_or_lt(a, b) with {
        inl(x) => { exact False.elim(h(x)) },
        inr(x) => { exact x },
    }
}
theorem ne_split(a: Nat, b: Nat, h: Not<a = b>): Or<lt(a, b), lt(b, a)> := by {
    cases le_or_lt(a, b) with {
        inl(x) => {
            cases le_or_lt(b, a) with {
                inl(y) => { exact False.elim(h(le_antisymm(a, b, x, y))) },
                inr(y) => { left; exact y },
            }
        },
        inr(x) => { right; exact x },
    }
}
theorem le_of_eq(a: Nat, b: Nat, h: a = b): le(a, b) := by { exists 0; exact h }
theorem le_of_succ_le_succ(a: Nat, b: Nat, h: le(Nat.succ(a), Nat.succ(b))): le(a, b) := by {
    cases h with { intro(k, hk) => { exists k; simp at hk; exact succ_inj(a + k, b, hk) } }
}
theorem not_succ_le_zero(k: Nat, h: le(Nat.succ(k), 0)): False := by {
    cases h with { intro(w, hw) => { simp at hw; exact succ_ne_zero(k + w, hw) } }
}
theorem zero_sub(n: Nat): nat_sub(0, n) = 0 := by {
    induction n with {
        zero => { rfl },
        succ(m, ih) => { show nat_pred(nat_sub(0, m)) = 0; rw [ih] },
    }
}
theorem succ_sub_succ(n: Nat, m: Nat): nat_sub(Nat.succ(n), Nat.succ(m)) = nat_sub(n, m) := by {
    induction m with {
        zero => { rfl },
        succ(k, ih) => {
            show nat_pred(nat_sub(Nat.succ(n), Nat.succ(k))) = nat_pred(nat_sub(n, k));
            rw [ih]
        },
    }
}
theorem sub_eq_zero_of_le(a: Nat, b: Nat): le(a, b) -> nat_sub(a, b) = 0 := by {
    induction a generalizing b with {
        zero => { intro h; exact zero_sub(b) },
        succ(k, ih) => {
            cases b with {
                zero => { intro h; exact False.elim(not_succ_le_zero(k, h)) },
                succ(m) => {
                    intro h;
                    rw [succ_sub_succ];
                    exact ih(m, le_of_succ_le_succ(k, m, h))
                },
            }
        },
    }
}
theorem sub_add_cancel(a: Nat, b: Nat): le(b, a) -> nat_sub(a, b) + b = a := by {
    induction b generalizing a with {
        zero => { intro h; rfl },
        succ(m, ih) => {
            cases a with {
                zero => { intro h; exact False.elim(not_succ_le_zero(m, h)) },
                succ(k) => {
                    intro h;
                    rw [succ_sub_succ];
                    simp;
                    exact congr_arg(Nat.succ, ih(k, le_of_succ_le_succ(m, k, h)))
                },
            }
        },
    }
}
theorem le_succ_self(a: Nat): le(a, Nat.succ(a)) := by { exists 1 }
theorem sub_cases(a: Nat, b: Nat): Or<And<le(a, b), nat_sub(a, b) = 0>, And<lt(b, a), nat_sub(a, b) + b = a>> := by {
    cases le_or_lt(a, b) with {
        inl(x) => { left; exact And.intro(x, sub_eq_zero_of_le(a, b, x)) },
        inr(x) => {
            right;
            exact And.intro(x, sub_add_cancel(a, b, le_trans(b, Nat.succ(b), a, le_succ_self(b), x)))
        },
    }
}
