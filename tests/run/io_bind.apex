// out: got 5
// out: sum 12
fn compute() -> IO<Nat> {
    do {
        let a <- pure(5);
        println(String.append("got ", Nat.toString(a)));
        let b <- pure(7);
        pure(a + b)
    }
}

fn main() -> IO<Unit> {
    do {
        let total <- compute();
        println(String.append("sum ", Nat.toString(total)))
    }
}
