//! A small named-variable term builder. Used by tests and by the prelude
//! until the elaborator exists; resolves names to de Bruijn indices.

use crate::env::KResult;
use crate::level::Level;
use crate::term::*;

#[derive(Clone, Debug)]
pub enum Raw {
    /// A bound name if one is in scope, otherwise a constant with no universe arguments.
    Var(String),
    Const(String, Vec<Level>),
    Sort(Level),
    App(Box<Raw>, Box<Raw>),
    Lam(Mult, String, Box<Raw>, Box<Raw>),
    Pi(Mult, String, Box<Raw>, Box<Raw>),
}

pub fn v(n: &str) -> Raw {
    Raw::Var(n.into())
}
pub fn c(n: &str) -> Raw {
    Raw::Var(n.into())
}
pub fn cl(n: &str, ls: Vec<Level>) -> Raw {
    Raw::Const(n.into(), ls)
}
pub fn sort_(l: Level) -> Raw {
    Raw::Sort(l)
}
pub fn prop() -> Raw {
    Raw::Sort(Level::Zero)
}
/// `Type` = `Sort 1`.
pub fn type_() -> Raw {
    Raw::Sort(Level::of_nat(1))
}
pub fn app_(f: Raw, args: Vec<Raw>) -> Raw {
    args.into_iter()
        .fold(f, |acc, a| Raw::App(Box::new(acc), Box::new(a)))
}
pub fn lam_(x: &str, ty: Raw, body: Raw) -> Raw {
    lam_m(Mult::Omega, x, ty, body)
}
pub fn lam_m(m: Mult, x: &str, ty: Raw, body: Raw) -> Raw {
    Raw::Lam(m, x.into(), Box::new(ty), Box::new(body))
}
pub fn pi_(x: &str, ty: Raw, body: Raw) -> Raw {
    pi_m(Mult::Omega, x, ty, body)
}
pub fn pi_m(m: Mult, x: &str, ty: Raw, body: Raw) -> Raw {
    Raw::Pi(m, x.into(), Box::new(ty), Box::new(body))
}
pub fn arrow(a: Raw, b: Raw) -> Raw {
    pi_("_", a, b)
}

impl Raw {
    pub fn build(&self) -> KResult<T> {
        self.go(&mut Vec::new())
    }

    fn go(&self, scope: &mut Vec<String>) -> KResult<T> {
        Ok(match self {
            Raw::Var(n) => match scope.iter().rposition(|s| s == n) {
                Some(p) => bvar((scope.len() - 1 - p) as u32),
                None => cnst(n.as_str().into(), vec![]),
            },
            Raw::Const(n, ls) => cnst(n.as_str().into(), ls.clone()),
            Raw::Sort(l) => sort(l.clone()),
            Raw::App(f, a) => app(f.go(scope)?, a.go(scope)?),
            Raw::Lam(m, x, ty, b) | Raw::Pi(m, x, ty, b) => {
                let ty = ty.go(scope)?;
                scope.push(x.clone());
                let b = b.go(scope);
                scope.pop();
                let b = b?;
                if matches!(self, Raw::Lam(..)) {
                    lam(*m, ty, b)
                } else {
                    pi(*m, ty, b)
                }
            }
        })
    }
}
