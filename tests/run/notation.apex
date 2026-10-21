// out: 7
// out: 14
// out: 37
// out: 11
// out: true
infixl 65 "+++" => add3;
infixr 60 "<>" => cat;
prefix 100 "~~" => double;
infix 50 "<=>" => same;

fn add3(a: Nat, b: Nat) -> Nat { a + b + 1 }
fn cat(a: Nat, b: Nat) -> Nat { a * 10 + b }
fn double(a: Nat) -> Nat { a + a }
fn same(a: Nat, b: Nat) -> Bool { a == b }

macro twice(x) => x + x;
macro swap_sub(a, b) => b - a;

theorem op_assoc(): 1 +++ 2 +++ 3 = 8 := rfl
theorem pre(): ~~ 4 = 8 := rfl

fn main() -> IO<Unit> {
    do {
        display(1 +++ 2 +++ 3 - 1);       // left-associative: (1 +++ 2) +++ 3 - 1
        display(~~ 7);
        display(1 <> 2 <> 7 + 0);          // right-associative: 1 <> (2 <> 7)
        display(twice(5) + 1);
        display(2 <=> 2)
    }
}
