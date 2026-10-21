// out: 7
// out: 2 1
// out: 13
// out: 3 40
// out: 3
// out: 2
// out: 30
// out: 2
// out: 2
// out: 0
struct Stack { items: List<Nat>, size: Nat }

impl Stack {
    fn new() -> Stack { Stack.mk(List.nil, 0) }

    fn push(&mut self, x: Nat) {
        self.items = List.cons(x, self.items);
        self.size += 1;
    }

    fn pop(&mut self) -> Nat {
        match self.items {
            List.nil => 0,
            List.cons(h, t) => {
                self.items = t;
                self.size -= 1;
                h
            }
        }
    }

    fn len(&self) -> Nat { self.size }
}

fn inc(n: &mut Nat) { n += 1; }

fn swap(a: &mut Nat, b: &mut Nat) {
    let t := a;
    a = b;
    b = t;
}

fn add_to(acc: &mut Nat, n: Nat, m: Nat) { acc += n * m; }

struct C { n: Nat, m: Nat }

fn bump(c: &mut C) {
    c.n += 1;
    c.m = c.m * 2;
}

trait Counter { fn tick(&mut self) -> Nat; }

struct Clock { t: Nat }

impl Counter for Clock {
    fn tick(&mut self) -> Nat {
        self.t += 1;
        self.t
    }
}

fn run_twice<K: Counter>(c: &mut K) -> Nat {
    c.tick();
    c.tick()
}

fn main() -> IO<Unit> {
    do {
        let mut x := 5;
        inc(&mut x);
        inc(&mut x);
        display(x);

        let mut a := 1;
        let mut b := 2;
        swap(&mut a, &mut b);
        println(String.append(Nat.toString(a), String.append(" ", Nat.toString(b))));

        let mut total := 0;
        add_to(&mut total, 3, 4);
        add_to(&mut total, 1, 1);
        display(total);

        let mut c := C.mk(1, 10);
        bump(&mut c);
        bump(&mut c);
        println(String.append(Nat.toString(c.n), String.append(" ", Nat.toString(c.m))));

        let mut s := Stack.new();
        s.push(10);
        s.push(20);
        s.push(30);
        display(s.len());
        let top := s.pop();
        display(s.len());
        display(top);

        let mut clock := Clock.mk(0);
        display(run_twice(&mut clock));
        display(clock.t);

        let mut empty := Stack.new();
        display(empty.pop());
    }
}
