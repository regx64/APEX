// expect: overlaps with an existing impl
trait Tag { fn tag(&self) -> Nat; }
impl<T> Tag for T { fn tag(&self) -> Nat { 0 } }
impl Tag for Nat { fn tag(&self) -> Nat { 1 } }
