// expect: ties the result to another parameter
fn f<'a>(v: &'a Nat, w: &Nat) -> &'a Nat { w }
