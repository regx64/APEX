//! The verifier accepts what the kernel accepts, and rejects what only an unchecked path let in.

use apex_kernel::builder::*;
use apex_kernel::prelude::add_prelude;
use apex_kernel::{Env, Level};
use apex_verify::{verify, Options};

fn env() -> Env {
    let mut e = Env::new();
    add_prelude(&mut e).unwrap();
    e
}

fn eq_nat(a: Raw, b: Raw) -> Raw {
    app_(cl("Eq", vec![Level::of_nat(1)]), vec![c("Nat"), a, b])
}
fn refl_nat(a: Raw) -> Raw {
    app_(cl("Eq.refl", vec![Level::of_nat(1)]), vec![c("Nat"), a])
}
fn nat(n: u64) -> Raw {
    (0..n).fold(c("Nat.zero"), |acc, _| app_(c("Nat.succ"), vec![acc]))
}

#[test]
fn accepts_a_checked_environment() {
    let mut e = env();
    // 2 + 2 = 4, by computation
    e.add_def(
        "two_plus_two",
        &[],
        eq_nat(app_(c("Nat.add"), vec![nat(2), nat(2)]), nat(4))
            .build()
            .unwrap(),
        refl_nat(nat(4)).build().unwrap(),
    )
    .unwrap();
    let r = verify(&e.export(), Options { accel: true }).expect("a checked environment verifies");
    assert!(r.definitions >= 1);
}

#[test]
fn rejects_a_wrong_proof_that_bypassed_the_kernel() {
    let mut e = env();
    // `2 + 2 = 5` with the proof `refl`, added without checking (as the proof cache does)
    e.add_def_trusted(
        "lie",
        &[],
        eq_nat(app_(c("Nat.add"), vec![nat(2), nat(2)]), nat(5))
            .build()
            .unwrap(),
        refl_nat(nat(4)).build().unwrap(),
    )
    .unwrap();
    let err = verify(&e.export(), Options { accel: true }).expect_err("the lie must be caught");
    assert!(err.contains("lie"), "{err}");
}

#[test]
fn rejects_garbage() {
    assert!(verify(b"nonsense", Options { accel: true }).is_err());
    let mut data = env().export();
    data.truncate(data.len() / 2);
    assert!(verify(&data, Options { accel: true }).is_err());
}
