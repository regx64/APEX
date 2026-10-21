theorem sym<A: Type, a: A, b: A>(h: a = b): b = a := Eq.symm(h)
theorem tr<A: Type, a: A, b: A, c: A>(h: a = b, g: b = c): a = c := Eq.trans(h, g)
theorem both<P: Prop, Q: Prop>(p: P, q: Q): And<P, Q> := And.intro(p, q)
theorem fst<P: Prop, Q: Prop>(h: And<P, Q>): P := And.left(h)
theorem orl<P: Prop, Q: Prop>(p: P): Or<P, Q> := Or.inl(p)
theorem triv(): True := True.intro
theorem exf<P: Prop>(h: False): P := False.elim(h)
theorem cg(n: Nat, m: Nat, h: n = m): Nat.succ(n) = Nat.succ(m) := congr_arg(Nat.succ, h)
