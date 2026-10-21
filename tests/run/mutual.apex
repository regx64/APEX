// out: 3
// out: 0
// out: 6
mutual {
    enum Tree<T> { Node(T, Forest<T>) }
    enum Forest<T> { Nil, Cons(Tree<T>, Forest<T>) }
}
mutual {
    fn size_tree<T>(t: Tree<T>) -> Nat {
        match t { Tree.Node(_, f) => 1 + size_forest(f) }
    }
    fn size_forest<T>(f: Forest<T>) -> Nat {
        match f {
            Forest.Nil => 0,
            Forest.Cons(t, r) => size_tree(t) + size_forest(r),
        }
    }
}
mutual {
    fn sum_tree(t: Tree<Nat>) -> Nat {
        match t { Tree.Node(x, f) => x + sum_forest(f) }
    }
    fn sum_forest(f: Forest<Nat>) -> Nat {
        match f {
            Forest.Nil => 0,
            Forest.Cons(t, r) => sum_tree(t) + sum_forest(r),
        }
    }
}
fn sample() -> Tree<Nat> {
    Tree.Node(1, Forest.Cons(Tree.Node(2, Forest.Nil), Forest.Cons(Tree.Node(3, Forest.Nil), Forest.Nil)))
}
fn main() -> IO<Unit> {
    do {
        display(size_tree(sample()));
        display(sum_forest(Forest.Nil));
        display(sum_tree(sample()));
    }
}
