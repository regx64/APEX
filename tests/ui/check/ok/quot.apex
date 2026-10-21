// Quotients compute: lift f h (mk r a) = f a, by the kernel's rule
theorem lift_mk<A: Type, B: Type>(r: A -> A -> Prop, f: A -> B, hf: forall(a: A, b: A) -> r(a, b) -> f(a) = f(b), a: A): Quot.lift(f, hf, Quot.mk(r, a)) = f(a) := rfl

// funext is derived from the quotient axiom
theorem ext_id(): (|x: Nat| x) = (|x: Nat| x + 0) := funext(|x: Nat| rfl)
theorem ext_pointwise(f: Nat -> Nat, g: Nat -> Nat, h: forall(x: Nat) -> f(x) = g(x)): f = g := funext(h)

theorem all_refl(): forall(n: Nat) -> n = n := |n: Nat| rfl
