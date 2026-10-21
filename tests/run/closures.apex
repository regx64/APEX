// out: 15
// out: 7
// out: 406
// out: 11
fn adder(n: Nat) -> Nat -> Nat { |x| x + n }

fn twice(f: Nat -> Nat, x: Nat) -> Nat { f(f(x)) }

fn compose(f: Nat -> Nat, g: Nat -> Nat) -> Nat -> Nat { |x| f(g(x)) }

fn main() -> IO<Unit> {
    do {
        display(adder(10)(5));
        display(twice(adder(3), 1));
        display(list_sum(list_map(range(4), adder(100))));
        display(compose(|a| a + 1, |b| b * 2)(5));
    }
}
