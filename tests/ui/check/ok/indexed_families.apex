// inductive predicates and indexed families (`enum Name<params>(indices): Sort`)
enum Even(n: Nat): Prop {
    Zero: Even(0),
    Add2<k: Nat>(Even(k)): Even(k + 2),
}

theorem even_four(): Even(4) := Even.Add2(Even.Add2(Even.Zero))
theorem even_plus2(n: Nat, h: Even(n)): Even(n + 2) := Even.Add2(h)

// induction on a proof of an indexed predicate: the index `n` is abstracted
theorem even_double(k: Nat): Even(k + k) := by {
    induction k with {
        zero => { exact Even.Zero },
        succ(j, ih) => {
            have e: Nat.succ(j) + Nat.succ(j) = j + j + 2 := by { omega };
            rw [e];
            exact Even.Add2(ih)
        },
    }
}

theorem even_zero_or_ge2(n: Nat, h: Even(n)): Or<n = 0, le(2, n)> := by {
    induction h with {
        Zero => { left; rfl },
        Add2(k, hk, ih) => { right; omega },
    }
}

// cases on the proof
theorem even_cases(n: Nat, h: Even(n)): Or<n = 0, Exists(|k: Nat| n = k + 2)> := by {
    cases h with {
        Zero => { left; rfl },
        Add2(k, hk) => { right; exists k },
    }
}

enum Vec<T>(n: Nat) {
    Nil: Vec<T, 0>,
    Cons<n: Nat>(T, Vec<T, n>): Vec<T, n + 1>,
}

theorem vec_build(): Vec<Nat, 2> := Vec.Cons(1, Vec.Cons(2, Vec.Nil))

// every vector of length `n` is built by `Nil` or `Cons`
theorem vec_zero_or_succ<T: Type>(n: Nat, v: Vec<T, n>): Or<n = 0, Exists(|m: Nat| n = m + 1)> := by {
    cases v with {
        Nil => { left; rfl },
        Cons(m, x, rest) => { right; exists m },
    }
}

// an index that is not a variable: each case carries an equation (`heq0`)
theorem even_not_one(h: Even(1)): False := by {
    cases h with {
        Zero => { omega },
        Add2(k, hk) => { omega },
    }
}

theorem even_three_is_false(h: Even(3)): False := by {
    cases h with {
        Zero => { omega },
        Add2(k, hk) => {
            // k + 2 = 3, so k = 1, and `Even(1)` is impossible
            have e: k = 1 := by { omega };
            rw [e] at hk;
            exact even_not_one(hk)
        },
    }
}
