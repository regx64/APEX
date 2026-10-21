// out: Node(Leaf, 3, Node(Leaf, 4, Leaf))
// out: true
// out: false
// out: true
// out: false
#[derive(BEq, Show, Ord)]
enum Tree { Leaf, Node(Tree, Nat, Tree) }

#[derive(BEq, Show)]
enum Expr<T> { Lit(T), Add(Expr<T>, Expr<T>) }

fn main() -> IO<Unit> {
    do {
        let t := Tree.Node(Tree.Leaf, 3, Tree.Node(Tree.Leaf, 4, Tree.Leaf));
        display(t);
        display(t == t);
        display(t == Tree.Leaf);
        display(Tree.Leaf < t);
        display(t < Tree.Leaf);
    }
}
