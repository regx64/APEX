// expect: cannot return `IO` yet
fn tick(c: &mut Nat) -> IO<Unit> { do { c += 1; } }
