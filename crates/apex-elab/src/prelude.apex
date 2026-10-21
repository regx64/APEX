// Surface-level prelude, elaborated at startup.

theorem rfl<A: Type, a: A>(): a = a := Eq.refl(a)

fn println(s: String) -> IO<Unit> {
    do {
        print(s);
        print("\n")
    }
}
