// expect: no implementation of `Add Bool`
fn twice_bad(f: Nat -> Bool) -> Nat { 1 }
fn f() -> Nat { twice_bad(|x| x + 1) }
