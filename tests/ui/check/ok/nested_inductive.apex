enum Rose { Node(Nat, List<Rose>) }
fn leaf(n: Nat) -> Rose { Rose.Node(n, List.nil) }
fn two() -> Rose { Rose.Node(1, [leaf(2), leaf(3)]) }
fn label(r: Rose) -> Nat { match r { Rose.Node(n, _) => n } }
fn kids(r: Rose) -> List<Rose> { match r { Rose.Node(_, ks) => ks } }
theorem l1(): label(two()) = 1 := by { rfl }
theorem k1(): list_len(kids(two())) = 2 := by { rfl }
theorem rose_cases(r: Rose): exists(n: Nat) -> exists(ks: List<Rose>) -> r = Rose.Node(n, ks) := by {
    cases r with { Node(n, ks) => { exists n; exists ks } }
}
mutual {
    fn size_rose(r: Rose) -> Nat {
        match r { Rose.Node(_, ks) => 1 + size_roses(ks) }
    }
    fn size_roses(ks: List<Rose>) -> Nat {
        match ks {
            List.nil => 0,
            List.cons(r, rest) => size_rose(r) + size_roses(rest),
        }
    }
}
theorem s1(): size_rose(two()) = 3 := by { rfl }
theorem s2(): size_roses([two(), leaf(5)]) = 4 := by { rfl }
enum Tree<T> { Node(T, List<Tree<T>>) }
enum Json { Arr(List<Json>), Num(Nat), Opt(Option<Json>) }
enum Deep { D(List<List<Deep>>) }
