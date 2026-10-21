// expect: cannot tell which implementation
// Even with a single impl, an unknown type is not inferred from it (adding a second impl later must not break this)
trait Default { fn default() -> Self; }
impl Default for Nat { fn default() -> Self { 0 } }
fn f() -> Nat { let x := Default.default(); 1 }
