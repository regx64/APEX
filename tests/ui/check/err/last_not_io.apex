// expect: type mismatch
fn main() -> IO<Unit> { do { let x <- pure(1); x } }
