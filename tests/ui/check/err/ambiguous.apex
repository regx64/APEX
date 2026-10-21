// expect: cannot tell which implementation
trait Default { fn default() -> Self; }
impl Default for Nat { fn default() -> Self { 0 } }
impl Default for Bool { fn default() -> Self { false } }
fn f() -> Nat { let x := Default.default(); 1 }
