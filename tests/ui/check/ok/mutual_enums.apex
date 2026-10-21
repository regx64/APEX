mutual {
    enum Tree<T> { Node(T, Forest<T>) }
    enum Forest<T> { Nil, Cons(Tree<T>, Forest<T>) }
}

fn leaf(x: Nat) -> Tree<Nat> { Tree.Node(x, Forest.Nil) }
fn two(x: Nat) -> Forest<Nat> { Forest.Cons(leaf(x), Forest.Cons(leaf(x), Forest.Nil)) }

fn root<T>(t: Tree<T>) -> T { match t { Tree.Node(x, _) => x } }
fn is_nil<T>(f: Forest<T>) -> Bool { match f { Forest.Nil => true, Forest.Cons(_, _) => false } }
theorem root_leaf(x: Nat): root(leaf(x)) = x := by { rfl }
theorem two_not_nil(x: Nat): is_nil(two(x)) = false := by { rfl }

theorem forest_cases<T>(f: Forest<T>): Or<f = Forest.Nil, Not<f = Forest.Nil>> := by {
    cases f with {
        Nil => { left; rfl },
        Cons(t, r) => { right; intro h; contradiction },
    }
}

theorem cons_inj<T>(a: Tree<T>, b: Tree<T>, r: Forest<T>, s: Forest<T>,
        h: Forest.Cons(a, r) = Forest.Cons(b, s)): a = b := by {
    injection h with h1 h2;
    exact h1
}
theorem succ_inj2(a: Nat, b: Nat, h: Nat.succ(a) = Nat.succ(b)): a = b := by {
    injection h with h1; exact h1
}
theorem zero_ne_succ(a: Nat, h: 0 = Nat.succ(a)): False := by { contradiction }

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
theorem size_leaf(x: Nat): size_tree(leaf(x)) = 1 := by { rfl }
theorem size_two(x: Nat): size_forest(two(x)) = 2 := by { rfl }
