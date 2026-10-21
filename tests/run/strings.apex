// out: 5
// out: true
// out: false
fn main() -> IO<Unit> {
    do {
        display(String.length("héllo"));
        display("abc" == "abc");
        display("abc" == "abd");
    }
}
