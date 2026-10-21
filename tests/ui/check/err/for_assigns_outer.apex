// expect: not declared `mut`
fn main() -> IO<Unit> { do { let mut t := 0; for i in range(3) { t += i; } display(t) } }
