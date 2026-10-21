// out: true
fn not(b: Bool) -> Bool {
    match b {
        true => false,
        false => true,
    }
}

fn is_zero(n: Nat) -> Bool {
    match n {
        0 => true,
        _ => false,
    }
}

fn main() -> Bool { if is_zero(0) { not(false) } else { false } }
