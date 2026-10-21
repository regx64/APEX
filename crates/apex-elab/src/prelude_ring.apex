// `ring`: a verified normalizer for commutative-semiring identities over `Nat` (reflection).
//
// An expression is reified to `RE` (atoms are numbered, `env` lists their values). `norm`
// turns it into a polynomial: a sorted list of (coefficient, monomial) pairs, a monomial being
// a sorted list of atom numbers. `norm_sound` says the polynomial has the expression's value, so
// two expressions with the same `norm` are equal (`ring_sound`); the kernel checks the premise
// `norm a = norm b` by computation. Completeness is not claimed, soundness is proved here.

enum RE { RConst(Nat), RVar(Nat), RAdd(RE, RE), RMul(RE, RE) }
enum Ord3 { OLt, OEq, OGt }

fn nth(env: List<Nat>, i: Nat) -> Nat {
    match env {
        List.nil => 0,
        List.cons(x, rest) => match i { 0 => x, Nat.succ(j) => nth(rest, j) },
    }
}
fn reval(env: List<Nat>, e: RE) -> Nat {
    match e {
        RE.RConst(n) => n,
        RE.RVar(i) => nth(env, i),
        RE.RAdd(a, b) => reval(env, a) + reval(env, b),
        RE.RMul(a, b) => reval(env, a) * reval(env, b),
    }
}
fn nat_cmp(a: Nat, b: Nat) -> Ord3 {
    match a {
        0 => match b { 0 => Ord3.OEq, Nat.succ(_) => Ord3.OLt },
        Nat.succ(a1) => match b { 0 => Ord3.OGt, Nat.succ(b1) => nat_cmp(a1, b1) },
    }
}
fn mono_val(env: List<Nat>, m: List<Nat>) -> Nat {
    match m { List.nil => 1, List.cons(x, r) => nth(env, x) * mono_val(env, r) }
}
fn mono_insert(x: Nat, m: List<Nat>) -> List<Nat> {
    match m {
        List.nil => List.cons(x, List.nil),
        List.cons(y, r) => match nat_cmp(x, y) {
            Ord3.OGt => List.cons(y, mono_insert(x, r)),
            _ => List.cons(x, List.cons(y, r)),
        },
    }
}
fn mono_mul(a: List<Nat>, b: List<Nat>) -> List<Nat> {
    match a { List.nil => b, List.cons(x, r) => mono_insert(x, mono_mul(r, b)) }
}
fn ord_then(o: Ord3, r: Ord3) -> Ord3 { match o { Ord3.OEq => r, _ => o } }
fn mono_cmp(a: List<Nat>, b: List<Nat>) -> Ord3 {
    match a {
        List.nil => match b { List.nil => Ord3.OEq, List.cons(_, _) => Ord3.OLt },
        List.cons(x, r) => match b {
            List.nil => Ord3.OGt,
            List.cons(y, s) => ord_then(nat_cmp(x, y), mono_cmp(r, s)),
        },
    }
}
fn poly_val(env: List<Nat>, p: List<Prod<Nat, List<Nat>>>) -> Nat {
    match p {
        List.nil => 0,
        List.cons(t, r) => Prod.fst(t) * mono_val(env, Prod.snd(t)) + poly_val(env, r),
    }
}
fn term_single(c: Nat, m: List<Nat>) -> List<Prod<Nat, List<Nat>>> {
    match c { 0 => List.nil, Nat.succ(c1) => List.cons(Prod.mk(Nat.succ(c1), m), List.nil) }
}
fn term_insert(c: Nat, m: List<Nat>, p: List<Prod<Nat, List<Nat>>>) -> List<Prod<Nat, List<Nat>>> {
    match p {
        List.nil => term_single(c, m),
        List.cons(t, r) => match c {
            0 => p,
            Nat.succ(c1) => match mono_cmp(m, Prod.snd(t)) {
                Ord3.OEq => List.cons(Prod.mk(Nat.succ(c1) + Prod.fst(t), m), r),
                Ord3.OLt => List.cons(Prod.mk(Nat.succ(c1), m), List.cons(t, r)),
                Ord3.OGt => List.cons(t, term_insert(Nat.succ(c1), m, r)),
            },
        },
    }
}
fn poly_add(p: List<Prod<Nat, List<Nat>>>, q: List<Prod<Nat, List<Nat>>>) -> List<Prod<Nat, List<Nat>>> {
    match p { List.nil => q, List.cons(t, r) => term_insert(Prod.fst(t), Prod.snd(t), poly_add(r, q)) }
}
fn poly_scale(c: Nat, m: List<Nat>, q: List<Prod<Nat, List<Nat>>>) -> List<Prod<Nat, List<Nat>>> {
    match q {
        List.nil => List.nil,
        List.cons(t, r) => term_insert(c * Prod.fst(t), mono_mul(m, Prod.snd(t)), poly_scale(c, m, r)),
    }
}
fn poly_mul(p: List<Prod<Nat, List<Nat>>>, q: List<Prod<Nat, List<Nat>>>) -> List<Prod<Nat, List<Nat>>> {
    match p {
        List.nil => List.nil,
        List.cons(t, r) => poly_add(poly_scale(Prod.fst(t), Prod.snd(t), q), poly_mul(r, q)),
    }
}
fn norm(e: RE) -> List<Prod<Nat, List<Nat>>> {
    match e {
        RE.RConst(n) => term_single(n, List.nil),
        RE.RVar(i) => term_single(1, List.cons(i, List.nil)),
        RE.RAdd(a, b) => poly_add(norm(a), norm(b)),
        RE.RMul(a, b) => poly_mul(norm(a), norm(b)),
    }
}

theorem nat_cmp_eq(a: Nat, b: Nat, h: nat_cmp(a, b) = Ord3.OEq): a = b := by {
    induction a generalizing b with {
        zero => {
            cases b with {
                zero => { rfl },
                succ(b1) => { simp at h; contradiction },
            }
        },
        succ(a1, ih) => {
            cases b with {
                zero => { simp at h; contradiction },
                succ(b1) => { simp at h; rw [ih(b1, h)] },
            }
        },
    }
}
theorem ord_then_eq(o: Ord3, r: Ord3, h: ord_then(o, r) = Ord3.OEq): o = Ord3.OEq /\ r = Ord3.OEq := by {
    cases o with {
        OLt => { simp at h; contradiction },
        OEq => { simp at h; constructor; rfl; exact h },
        OGt => { simp at h; contradiction },
    }
}
theorem mono_cmp_eq(a: List<Nat>, b: List<Nat>, h: mono_cmp(a, b) = Ord3.OEq): a = b := by {
    induction a generalizing b with {
        nil => {
            cases b with {
                nil => { rfl },
                cons(y, s) => { simp at h; contradiction },
            }
        },
        cons(x, r, ih) => {
            cases b with {
                nil => { simp at h; contradiction },
                cons(y, s) => {
                    simp at h;
                    obtain (h1, h2) := ord_then_eq(nat_cmp(x, y), mono_cmp(r, s), h);
                    rw [nat_cmp_eq(x, y, h1), ih(s, h2)]
                },
            }
        },
    }
}
theorem mul_left_comm(a: Nat, b: Nat, c: Nat): a * (b * c) = b * (a * c) := by {
    rw [<- mul_assoc, mul_comm(a, b), mul_assoc]
}
theorem mono_val_insert(env: List<Nat>, x: Nat, m: List<Nat>):
        mono_val(env, mono_insert(x, m)) = nth(env, x) * mono_val(env, m) := by {
    induction m with {
        nil => { simp },
        cons(y, r, ih) => {
            simp [mono_insert];
            cases hc : nat_cmp(x, y) with {
                OLt => { rfl },
                OEq => { rfl },
                OGt => { simp [ih]; exact mul_left_comm(nth(env, y), nth(env, x), mono_val(env, r)) },
            }
        },
    }
}
theorem mono_val_mul(env: List<Nat>, a: List<Nat>, b: List<Nat>):
        mono_val(env, mono_mul(a, b)) = mono_val(env, a) * mono_val(env, b) := by {
    induction a with {
        nil => { simp [mono_mul, mono_val] },
        cons(x, r, ih) => {
            simp [mono_mul];
            rw [mono_val_insert, ih];
            rw [mul_assoc]
        },
    }
}
theorem poly_val_single(env: List<Nat>, c: Nat, m: List<Nat>):
        poly_val(env, term_single(c, m)) = c * mono_val(env, m) := by {
    cases c with {
        zero => { simp [term_single, poly_val] },
        succ(c1) => { simp [term_single, poly_val] },
    }
}
theorem poly_val_insert(env: List<Nat>, c: Nat, m: List<Nat>, p: List<Prod<Nat, List<Nat>>>):
        poly_val(env, term_insert(c, m, p)) = c * mono_val(env, m) + poly_val(env, p) := by {
    induction p with {
        nil => { simp [term_insert, poly_val_single, poly_val] },
        cons(t, r, ih) => {
            cases c with {
                zero => { simp [term_insert] },
                succ(c1) => {
                    simp [term_insert];
                    cases hc : mono_cmp(m, Prod.snd(t)) with {
                        OLt => { simp [poly_val] },
                        OEq => {
                            rw [mono_cmp_eq(m, Prod.snd(t), hc)];
                            simp [poly_val];
                            rw [add_mul]; omega
                        },
                        OGt => {
                            simp [poly_val, ih];
                            rw [add_left_comm]
                        },
                    }
                },
            }
        },
    }
}
theorem poly_val_add(env: List<Nat>, p: List<Prod<Nat, List<Nat>>>, q: List<Prod<Nat, List<Nat>>>):
        poly_val(env, poly_add(p, q)) = poly_val(env, p) + poly_val(env, q) := by {
    induction p with {
        nil => { simp [poly_add, poly_val] },
        cons(t, r, ih) => {
            simp [poly_add];
            rw [poly_val_insert, ih];
            omega
        },
    }
}
theorem mul_mul_mul_comm(a: Nat, b: Nat, c: Nat, d: Nat): (a * b) * (c * d) = (a * c) * (b * d) := by {
    rw [mul_assoc, <- mul_assoc(b, c, d), mul_comm(b, c), mul_assoc(c, b, d), <- mul_assoc]
}
theorem poly_val_scale(env: List<Nat>, c: Nat, m: List<Nat>, q: List<Prod<Nat, List<Nat>>>):
        poly_val(env, poly_scale(c, m, q)) = (c * mono_val(env, m)) * poly_val(env, q) := by {
    induction q with {
        nil => { simp [poly_scale, poly_val] },
        cons(t, r, ih) => {
            simp [poly_scale];
            rw [poly_val_insert, mono_val_mul, ih];
            rw [mul_add, mul_mul_mul_comm]
        },
    }
}
theorem poly_val_mul(env: List<Nat>, p: List<Prod<Nat, List<Nat>>>, q: List<Prod<Nat, List<Nat>>>):
        poly_val(env, poly_mul(p, q)) = poly_val(env, p) * poly_val(env, q) := by {
    induction p with {
        nil => { simp [poly_mul, poly_val] },
        cons(t, r, ih) => {
            simp [poly_mul];
            rw [poly_val_add, poly_val_scale, ih];
            rw [add_mul]
        },
    }
}
theorem norm_sound(env: List<Nat>, e: RE): poly_val(env, norm(e)) = reval(env, e) := by {
    induction e with {
        RConst(n) => { simp [norm, reval]; rw [poly_val_single]; simp [mono_val] },
        RVar(i) => { simp [norm, reval] },
        RAdd(a, b, iha, ihb) => { simp [norm, reval]; rw [poly_val_add, iha, ihb] },
        RMul(a, b, iha, ihb) => { simp [norm, reval]; rw [poly_val_mul, iha, ihb] },
    }
}
theorem ring_sound(env: List<Nat>, a: RE, b: RE, h: norm(a) = norm(b)): reval(env, a) = reval(env, b) := by {
    rw [<- norm_sound(env, a), <- norm_sound(env, b), h]
}
