// Small data types of the standard library: `Option`, subtypes and dependent pairs.
// (Loaded when a program mentions one of them without declaring its own.)

enum Option<T> { None, Some(T) }
/// `{ x : A // P x }`
struct Subtype<A, P: A -> Prop> { val: A, property: P(val) }
/// `Σ x : A, B x`
struct Sigma<A, B: A -> Type> { fst: A, snd: B(fst) }

fn option_map<A, B>(o: Option<A>, f: A -> B) -> Option<B> {
    match o { Option.None => Option.None, Option.Some(x) => Option.Some(f(x)) }
}
fn option_get_or<A>(o: Option<A>, d: A) -> A { match o { Option.None => d, Option.Some(x) => x } }
fn option_bind<A, B>(o: Option<A>, f: A -> Option<B>) -> Option<B> {
    match o { Option.None => Option.None, Option.Some(x) => f(x) }
}
fn option_is_some<A>(o: Option<A>) -> Bool { match o { Option.None => false, Option.Some(_) => true } }
impl<T: Show> Show for Option<T> {
    fn show(&self) -> String {
        match self {
            Option.None => "None",
            Option.Some(x) => String.append("Some(", String.append(x.show(), ")")),
        }
    }
}
impl<T: BEq> BEq for Option<T> {
    fn beq(self, other: Self) -> Bool {
        match self {
            Option.None => match other { Option.None => true, Option.Some(_) => false },
            Option.Some(x) => match other { Option.None => false, Option.Some(y) => x == y },
        }
    }
}
theorem option_map_none<A, B>(f: A -> B): option_map(Option.None, f) = Option.None := by { rfl }
theorem option_map_some<A, B>(x: A, f: A -> B): option_map(Option.Some(x), f) = Option.Some(f(x)) := by { rfl }
theorem some_inj<A>(x: A, y: A, h: Option.Some(x) = Option.Some(y)): x = y := by {
    injection h with e; exact e
}
theorem none_ne_some<A>(x: A, h: Option.None = Option.Some(x)): False := by { contradiction }
