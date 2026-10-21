// out: [0, 1, 2, 3, 4]
// out: 10
// out: [2, 4, 6]
// out: [0, 3, 6, 9]
// out: 10
// out: [3, 2, 1, 0]
// out: i = 0
// out: i = 1
// out: i = 2
// out: a
// out: b
// out: 3
// out: 3
// out: 2
// out: 0
fn main() -> IO<Unit> {
    do {
        display(range(5));
        display(list_sum(range(5)));
        display(list_map([1, 2, 3], |x| x * 2));
        display(list_filter(range(10), |x| x % 3 == 0));
        display(list_foldl([1, 2, 3, 4], 0, |acc, x| acc + x));
        display(list_reverse(range(4)));
        for i in range(3) {
            println(String.append("i = ", Nat.toString(i)))
        }
        for w in ["a", "b"] {
            println(w)
        }
        display(list_len(["x", "y", "z"]));
        display(17 / 5);
        display(17 % 5);
        display(1 / 0);
    }
}
