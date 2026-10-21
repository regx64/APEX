// out: Hello, APEX!
// out: answer: 42
fn main() -> IO<Unit> {
    do {
        println("Hello, APEX!");
        let n := 6 * 7;
        println(String.append("answer: ", Nat.toString(n)));
    }
}
