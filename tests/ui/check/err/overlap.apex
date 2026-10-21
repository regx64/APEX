// expect: overlaps with an existing impl
impl Show for Nat { fn show(&self) -> String { "again" } }
