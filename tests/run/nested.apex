// out: 3
enum Tree<T> { Node(T, List<Tree<T>>) }
enum Json { Arr(List<Json>), Num(Nat), Opt(Option<Json>) }
enum Deep { D(List<List<Deep>>) }
fn mk() -> Tree<Nat> { Tree.Node(1, [Tree.Node(2, List.nil)]) }
mutual {
    fn tsum(t: Tree<Nat>) -> Nat { match t { Tree.Node(x, ks) => x + tsums(ks) } }
    fn tsums(ks: List<Tree<Nat>>) -> Nat {
        match ks { List.nil => 0, List.cons(t, r) => tsum(t) + tsums(r) }
    }
}
theorem t1(): tsum(mk()) = 3 := by { rfl }
fn main() -> IO<Unit> { display(tsum(mk())) }
