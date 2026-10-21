//! The trusted kernel: core terms, universe levels, a type checker with
//! quantitative (0/1/ω) binders, and inductive types with generated recursors.

pub mod below;
pub mod builder;
pub mod env;
pub mod inductive;
pub mod level;
mod nested;
pub mod prelude;
pub mod ser;
pub mod tc;
pub mod term;

pub use env::{kerr, Decl, Env, KResult, KernelError, NestedInfo};
pub use inductive::{InductiveDecl, MutualDecl, TypeDecl};
pub use level::Level;
pub use tc::TypeChecker;
pub use term::{Mult, Name, Term, T};
