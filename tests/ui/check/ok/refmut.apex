// Functions with `&mut` parameters are pure functions returning (result, updated arguments),
// so they can be proved about like any other.
fn inc(n: &mut Nat) { n += 1; }

fn add_to(acc: &mut Nat, n: Nat, m: Nat) { acc += n * m; }

fn swap(a: &mut Nat, b: &mut Nat) {
    let t := a;
    a = b;
    b = t;
}

struct Stack { items: List<Nat>, size: Nat }

impl Stack {
    fn new() -> Stack { Stack.mk(List.nil, 0) }
    fn push(&mut self, x: Nat) {
        self.items = List.cons(x, self.items);
        self.size += 1;
    }
    fn len(&self) -> Nat { self.size }
}

fn count_to_three() -> Nat {
    let mut s := Stack.new();
    s.push(1);
    s.push(2);
    s.push(3);
    s.len()
}

fn twice_inc(start: Nat) -> Nat {
    let mut x := start;
    inc(&mut x);
    inc(&mut x);
    x
}

fn swapped() -> Nat {
    let mut a := 3;
    let mut b := 8;
    swap(&mut a, &mut b);
    a * 10 + b
}

// a pure function that borrows shared references
fn first_or(v: &List<Nat>, d: Nat) -> Nat {
    match v {
        List.nil => d,
        List.cons(h, _) => h,
    }
}

theorem count_ex(): count_to_three() = 3 := rfl
theorem twice_ex(): twice_inc(5) = 7 := rfl
theorem swap_ex(): swapped() = 83 := rfl
theorem first_ex(): first_or(&[4, 5], 0) = 4 := rfl
