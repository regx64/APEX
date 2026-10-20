//! Core terms in locally nameless form: bound variables are de Bruijn
//! indices, free variables (`FVar`) carry a unique id and are used while
//! traversing binders.

use crate::level::Level;
use std::fmt;
use std::rc::Rc;

pub type Name = Rc<str>;
pub type T = Rc<Term>;

/// Binder multiplicity (quantitative type theory).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum Mult {
    /// Erased: only usable in types and proofs.
    Zero,
    /// Linear: used exactly once at runtime.
    One,
    /// Unrestricted.
    Omega,
}

impl Mult {
    pub fn plus(self, o: Mult) -> Mult {
        match (self, o) {
            (Mult::Zero, x) | (x, Mult::Zero) => x,
            _ => Mult::Omega,
        }
    }

    pub fn times(self, o: Mult) -> Mult {
        match (self, o) {
            (Mult::Zero, _) | (_, Mult::Zero) => Mult::Zero,
            (Mult::One, x) | (x, Mult::One) => x,
            _ => Mult::Omega,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum Term {
    BVar(u32),
    FVar(u32),
    Sort(Level),
    Const(Name, Vec<Level>),
    App(T, T),
    Lam(Mult, T, T),
    Pi(Mult, T, T),
    /// `let x :m ty := val; body`
    Let(Mult, T, T, T),
}

pub fn bvar(i: u32) -> T {
    Rc::new(Term::BVar(i))
}
pub fn fvar(i: u32) -> T {
    Rc::new(Term::FVar(i))
}
pub fn sort(l: Level) -> T {
    Rc::new(Term::Sort(l))
}
pub fn cnst(n: Name, ls: Vec<Level>) -> T {
    Rc::new(Term::Const(n, ls))
}
pub fn app(f: T, a: T) -> T {
    Rc::new(Term::App(f, a))
}
pub fn lam(m: Mult, ty: T, b: T) -> T {
    Rc::new(Term::Lam(m, ty, b))
}
pub fn pi(m: Mult, ty: T, b: T) -> T {
    Rc::new(Term::Pi(m, ty, b))
}
pub fn let_(m: Mult, ty: T, v: T, b: T) -> T {
    Rc::new(Term::Let(m, ty, v, b))
}

pub fn mk_apps(f: &T, args: &[T]) -> T {
    args.iter().fold(f.clone(), |acc, a| app(acc, a.clone()))
}

/// Split `f a b c` into `(f, [a, b, c])`.
pub fn app_spine(t: &T) -> (T, Vec<T>) {
    let mut args = Vec::new();
    let mut cur = t.clone();
    while let Term::App(f, a) = &*cur.clone() {
        args.push(a.clone());
        cur = f.clone();
    }
    args.reverse();
    (cur, args)
}

/// Replace `BVar(0)` in `t` by `val` (which must have no loose bound variables).
pub fn instantiate(t: &T, val: &T) -> T {
    inst_at(t, val, 0)
}

fn inst_at(t: &T, val: &T, d: u32) -> T {
    match &**t {
        Term::BVar(i) => {
            if *i == d {
                val.clone()
            } else if *i > d {
                bvar(i - 1)
            } else {
                t.clone()
            }
        }
        Term::FVar(_) | Term::Sort(_) | Term::Const(..) => t.clone(),
        Term::App(f, a) => app(inst_at(f, val, d), inst_at(a, val, d)),
        Term::Lam(m, ty, b) => lam(*m, inst_at(ty, val, d), inst_at(b, val, d + 1)),
        Term::Pi(m, ty, b) => pi(*m, inst_at(ty, val, d), inst_at(b, val, d + 1)),
        Term::Let(m, ty, v, b) => let_(
            *m,
            inst_at(ty, val, d),
            inst_at(v, val, d),
            inst_at(b, val, d + 1),
        ),
    }
}

/// Replace `fvars[j]` by the bound variable that refers to it when `t` is
/// placed under `fvars.len()` binders (the last fvar is the innermost).
pub fn abstract_fvars(t: &T, fvars: &[u32]) -> T {
    if fvars.is_empty() {
        return t.clone();
    }
    abs_at(t, fvars, 0)
}

fn abs_at(t: &T, fvars: &[u32], d: u32) -> T {
    match &**t {
        Term::FVar(id) => match fvars.iter().position(|x| x == id) {
            Some(j) => bvar(d + (fvars.len() - 1 - j) as u32),
            None => t.clone(),
        },
        Term::BVar(_) | Term::Sort(_) | Term::Const(..) => t.clone(),
        Term::App(f, a) => app(abs_at(f, fvars, d), abs_at(a, fvars, d)),
        Term::Lam(m, ty, b) => lam(*m, abs_at(ty, fvars, d), abs_at(b, fvars, d + 1)),
        Term::Pi(m, ty, b) => pi(*m, abs_at(ty, fvars, d), abs_at(b, fvars, d + 1)),
        Term::Let(m, ty, v, b) => let_(
            *m,
            abs_at(ty, fvars, d),
            abs_at(v, fvars, d),
            abs_at(b, fvars, d + 1),
        ),
    }
}

pub fn contains_const(t: &T, name: &str) -> bool {
    match &**t {
        Term::Const(n, _) => &**n == name,
        Term::App(f, a) => contains_const(f, name) || contains_const(a, name),
        Term::Lam(_, ty, b) | Term::Pi(_, ty, b) => {
            contains_const(ty, name) || contains_const(b, name)
        }
        Term::Let(_, ty, v, b) => {
            contains_const(ty, name) || contains_const(v, name) || contains_const(b, name)
        }
        _ => false,
    }
}

pub fn contains_fvar(t: &T, id: u32) -> bool {
    match &**t {
        Term::FVar(i) => *i == id,
        Term::App(f, a) => contains_fvar(f, id) || contains_fvar(a, id),
        Term::Lam(_, ty, b) | Term::Pi(_, ty, b) => contains_fvar(ty, id) || contains_fvar(b, id),
        Term::Let(_, ty, v, b) => {
            contains_fvar(ty, id) || contains_fvar(v, id) || contains_fvar(b, id)
        }
        _ => false,
    }
}

pub fn instantiate_levels(t: &T, params: &[Name], ls: &[Level]) -> T {
    if params.is_empty() {
        return t.clone();
    }
    match &**t {
        Term::Sort(l) => sort(l.instantiate(params, ls)),
        Term::Const(n, lv) => cnst(
            n.clone(),
            lv.iter().map(|l| l.instantiate(params, ls)).collect(),
        ),
        Term::App(f, a) => app(
            instantiate_levels(f, params, ls),
            instantiate_levels(a, params, ls),
        ),
        Term::Lam(m, ty, b) => lam(
            *m,
            instantiate_levels(ty, params, ls),
            instantiate_levels(b, params, ls),
        ),
        Term::Pi(m, ty, b) => pi(
            *m,
            instantiate_levels(ty, params, ls),
            instantiate_levels(b, params, ls),
        ),
        Term::Let(m, ty, v, b) => let_(
            *m,
            instantiate_levels(ty, params, ls),
            instantiate_levels(v, params, ls),
            instantiate_levels(b, params, ls),
        ),
        Term::BVar(_) | Term::FVar(_) => t.clone(),
    }
}

pub fn collect_level_params(t: &T, out: &mut Vec<Name>) {
    match &**t {
        Term::Sort(l) => l.collect_params(out),
        Term::Const(_, ls) => ls.iter().for_each(|l| l.collect_params(out)),
        Term::App(f, a) => {
            collect_level_params(f, out);
            collect_level_params(a, out);
        }
        Term::Lam(_, ty, b) | Term::Pi(_, ty, b) => {
            collect_level_params(ty, out);
            collect_level_params(b, out);
        }
        Term::Let(_, ty, v, b) => {
            collect_level_params(ty, out);
            collect_level_params(v, out);
            collect_level_params(b, out);
        }
        Term::BVar(_) | Term::FVar(_) => {}
    }
}

fn mult_prefix(m: Mult) -> &'static str {
    match m {
        Mult::Zero => "0 ",
        Mult::One => "1 ",
        Mult::Omega => "",
    }
}

/// Pretty-print, naming free variables with `names`.
pub fn fmt_term(t: &T, names: &dyn Fn(u32) -> String) -> String {
    let go = |x: &T| fmt_term(x, names);
    match &**t {
        Term::BVar(i) => format!("#{i}"),
        Term::FVar(i) => names(*i),
        Term::Sort(l) => {
            if l.is_zero() {
                "Prop".into()
            } else {
                format!("Sort {l}")
            }
        }
        Term::Const(n, ls) if ls.is_empty() => n.to_string(),
        Term::Const(n, ls) => {
            format!(
                "{n}.{{{}}}",
                ls.iter()
                    .map(|l| l.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
        Term::App(..) => {
            let (f, args) = app_spine(t);
            let mut s = format!("({}", go(&f));
            for a in &args {
                s.push(' ');
                s.push_str(&go(a));
            }
            s.push(')');
            s
        }
        Term::Lam(m, ty, b) => format!("(fun {}{} => {})", mult_prefix(*m), go(ty), go(b)),
        Term::Pi(m, ty, b) => format!("({}{} -> {})", mult_prefix(*m), go(ty), go(b)),
        Term::Let(m, ty, v, b) => format!(
            "(let {}{} := {}; {})",
            mult_prefix(*m),
            go(ty),
            go(v),
            go(b)
        ),
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&fmt_term(&Rc::new(self.clone()), &|i| format!("_f{i}")))
    }
}
