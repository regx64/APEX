theorem two_eq(): 1 + 1 = 2 := rfl

theorem add_zero(n: Nat): n + 0 = n := rfl

theorem mul_one_zero(): 1 * 0 = 0 := rfl

theorem refl_example<A: Type>(a: A): a = a := rfl

fn use_it() -> Nat { 3 }

theorem use_it_eq(): use_it() = 3 := rfl
