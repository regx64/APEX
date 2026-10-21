theorem s1(a: Nat, b: Nat, h: a = b): b + 0 = a := by { subst h; rfl }
theorem s2(a: Nat, b: Nat, h: a = b): b + 0 = a := by { subst a; rfl }
theorem r1<P: Prop, Q: Prop>(h: P /\ Q): Q /\ P := by {
    obtain (p, q) := h;
    constructor; exact q; exact p
}
theorem r2<P: Prop, Q: Prop>(h: P \/ Q): Q \/ P := by {
    rcases h with p | q;
    right; exact p;
    left; exact q
}
theorem r3(h: exists(k: Nat) -> k + k = 4): exists(j: Nat) -> j + j = 4 := by {
    obtain (w, hw) := h;
    exists w; exact hw
}
theorem r4<P: Prop, Q: Prop, R: Prop>(h: P /\ Q /\ R): R := by {
    obtain (p, q, r) := h; exact r
}
theorem ri<P: Prop, Q: Prop>(): P /\ Q -> Q := by { rintro (p, q); exact q }
theorem ri2<P: Prop, Q: Prop>(): P \/ Q -> Q \/ P := by {
    rintro (p | q);
    right; exact p;
    left; exact q
}
theorem bc(n: Nat): Or<n = 0, n != 0> := by {
    by_cases h : n = 0;
    left; exact h;
    right; exact h
}
theorem bcon<P: Prop>(h: Not<Not<P>>): P := by {
    by_contra hn;
    exact h(hn)
}
theorem sp(f: forall(x: Nat) -> x = x /\ x + 0 = x): 3 + 0 = 3 := by {
    specialize f(3);
    obtain (_, h2) := f;
    exact h2
}
theorem rf<P: Prop, Q: Prop>(p: P, q: Q): P /\ Q := by {
    refine And.intro(p, _);
    exact q
}
theorem fx(f: Nat -> Nat, g: Nat -> Nat, h: forall(x: Nat) -> f(x) = g(x)): f = g := by {
    funext x;
    exact h(x)
}
theorem cg(a: Nat, b: Nat, h: a = b): Nat.succ(a + 1) = Nat.succ(b + 1) := by {
    congr;
    congr;
    exact h
}
theorem ca(a: Nat, b: Nat, h: a = b): a + 0 = b := by {
    calc {
        a + 0 = a := by { rfl };
        _ = b := h
    }
}
theorem ca2(a: Nat, b: Nat, c: Nat, h1: a <= b, h2: b = c): a <= c := by {
    calc {
        a <= b := h1;
        _ = c := h2
    }
}
theorem ca3(a: Nat, b: Nat, h1: lt(a, b)): lt(a, b + 1) := by {
    calc {
        lt(a, b) := h1;
        _ <= b + 1 := by { omega }
    }
}
theorem tr1(a: Nat): a + 0 = a := by { trivial }
theorem tr2<P: Prop>(h: P): P := by { trivial }
