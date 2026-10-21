// `auto`: backtracking proof search
theorem and_swap<P: Prop, Q: Prop>(h: And<P, Q>): And<Q, P> := by { auto }
theorem or_swap<P: Prop, Q: Prop>(h: Or<P, Q>): Or<Q, P> := by { auto }
theorem imp_chain<P: Prop, Q: Prop, R: Prop>(f: P -> Q, g: Q -> R): P -> R := by { auto }
theorem exists_and<P: Prop>(h: Exists(|n: Nat| And(n = 3, P))): P := by { auto }
theorem contra<P: Prop>(h: False): P := by { auto }
theorem not_not_intro<P: Prop>(p: P): Not<Not<P>> := by { auto }
theorem trans3(a: Nat, b: Nat, c: Nat, d: Nat, h1: a = b, h2: b = c, h3: c = d): a = d := by { auto }
theorem arith(x: Nat, y: Nat, h: lt(x, y)): And<le(x, y), Not<y = x>> := by { auto }
theorem mixed<P: Prop, Q: Prop>(hp: P, h: P -> And<Q, Q>): Or<Q, False> := by { auto }
