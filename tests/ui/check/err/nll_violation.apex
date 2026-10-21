// expect: cannot borrow `bob` as mutable because it is also borrowed as immutable
struct Account { id: Nat, balance: Nat }
fn deposit(a: &mut Account, n: Nat) { a.balance += n; }
fn balance(a: &Account) -> Nat { a.balance }
fn richest<'a>(x: &'a Account, y: &'a Account) -> &'a Account {
    if x.balance > y.balance { x } else { y }
}
fn f() -> Nat {
    let mut alice := Account.mk(1, 100);
    let mut bob := Account.mk(2, 50);
    let r := richest(&alice, &bob);
    deposit(&mut bob, 100);
    balance(r)
}
