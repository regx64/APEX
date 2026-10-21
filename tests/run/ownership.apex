// out: 125
// out: 150
// out: 7
// out: 100
// out: 1
// out: 2
// out: 3
struct Account { id: Nat, balance: Nat }

fn deposit(a: &mut Account, n: Nat) { a.balance += n; }

fn balance(a: &Account) -> Nat { a.balance }

// the result borrows from one of the two arguments: say so with a lifetime
fn richest<'a>(x: &'a Account, y: &'a Account) -> &'a Account {
    if x.balance > y.balance { x } else { y }
}

// `own`: a value that is consumed exactly once, and handed on to the next owner
fn finish(own ticket: Nat) -> Nat { ticket }

fn redeem(own ticket: Nat) -> Nat { finish(ticket) }

// elision: one borrowed parameter, so the result borrows from it
fn first_or<'a>(xs: &'a List<Nat>, d: &'a Nat) -> &'a Nat {
    match xs {
        List.nil => d,
        List.cons(h, _) => h,
    }
}

fn main() -> IO<Unit> {
    do {
        let mut alice := Account.mk(1, 100);
        let mut bob := Account.mk(2, 50);
        deposit(&mut alice, 25);
        let r := richest(&alice, &bob);
        display(balance(r));
        // `r` is not used again, so its borrow of `bob` is over: this is allowed
        deposit(&mut bob, 100);
        display(balance(&bob));
        display(redeem(7));

        let xs := [100, 200];
        let zero := 0;
        display(*first_or(&xs, &zero));

        let mut total := 0;
        for x in [1, 2] {
            println(Nat.toString(x));
        }
        total += 3;
        display(total);
    }
}
