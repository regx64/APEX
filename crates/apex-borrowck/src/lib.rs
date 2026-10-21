//! Borrow checking for APEX: how functions take and return references, and
//! (in `check`) whether a body uses them without creating aliases.
//!
//! References have value semantics (see `docs/OWNERSHIP.md`): `&mut T` is
//! copy-in / copy-out, so the checker's job is to reject programs where an alias
//! would make that differ from pointer semantics.

mod check;
mod sig;

pub use check::{check_fn, Diag};
pub use sig::{callee_of, param_kind, Callee, ParamKind, RetKind, SigError};
