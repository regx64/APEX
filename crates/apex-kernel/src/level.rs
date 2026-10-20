//! Universe levels. Comparison goes through a normal form: a set of
//! `(base, offset)` atoms meaning `max(base_i + offset_i)`.

use crate::term::Name;
use std::fmt;
use std::rc::Rc;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Level {
    Zero,
    Succ(Rc<Level>),
    Max(Rc<Level>, Rc<Level>),
    IMax(Rc<Level>, Rc<Level>),
    Param(Name),
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Base {
    Zero,
    Param(Name),
    /// An `imax` whose right side may be zero; compared structurally.
    Stuck(Level),
}

type Atoms = Vec<(Base, u32)>;

impl Level {
    pub fn zero() -> Level {
        Level::Zero
    }
    pub fn succ(self) -> Level {
        Level::Succ(Rc::new(self))
    }
    pub fn max(a: Level, b: Level) -> Level {
        Level::Max(Rc::new(a), Rc::new(b))
    }
    pub fn imax(a: Level, b: Level) -> Level {
        Level::IMax(Rc::new(a), Rc::new(b))
    }
    pub fn param(n: &str) -> Level {
        Level::Param(n.into())
    }
    pub fn of_nat(n: u32) -> Level {
        (0..n).fold(Level::Zero, |l, _| l.succ())
    }

    pub fn instantiate(&self, params: &[Name], args: &[Level]) -> Level {
        match self {
            Level::Zero => Level::Zero,
            Level::Succ(l) => l.instantiate(params, args).succ(),
            Level::Max(a, b) => {
                Level::max(a.instantiate(params, args), b.instantiate(params, args))
            }
            Level::IMax(a, b) => {
                Level::imax(a.instantiate(params, args), b.instantiate(params, args))
            }
            Level::Param(n) => match params.iter().position(|p| p == n) {
                Some(i) => args[i].clone(),
                None => self.clone(),
            },
        }
    }

    pub fn collect_params(&self, out: &mut Vec<Name>) {
        match self {
            Level::Zero => {}
            Level::Succ(l) => l.collect_params(out),
            Level::Max(a, b) | Level::IMax(a, b) => {
                a.collect_params(out);
                b.collect_params(out);
            }
            Level::Param(n) => out.push(n.clone()),
        }
    }

    fn norm(&self) -> Atoms {
        match self {
            Level::Zero => vec![(Base::Zero, 0)],
            Level::Param(n) => vec![(Base::Param(n.clone()), 0)],
            Level::Succ(l) => l.norm().into_iter().map(|(b, k)| (b, k + 1)).collect(),
            Level::Max(a, b) => {
                let mut v = a.norm();
                v.extend(b.norm());
                simplify(v)
            }
            Level::IMax(a, b) => {
                let (na, nb) = (a.norm(), b.norm());
                if nb.iter().any(|(_, k)| *k >= 1) {
                    // right side is never zero: imax = max
                    let mut v = na;
                    v.extend(nb);
                    simplify(v)
                } else if nb == vec![(Base::Zero, 0)] {
                    nb
                } else {
                    let l = Level::imax(from_atoms(&na), from_atoms(&nb));
                    vec![(Base::Stuck(l), 0)]
                }
            }
        }
    }

    /// Conservative: `true` only when `self <= o` for every assignment.
    pub fn leq(&self, o: &Level) -> bool {
        let (a, b) = (self.norm(), o.norm());
        a.iter().all(|(b1, k1)| {
            b.iter()
                .any(|(b2, k2)| k1 <= k2 && (b1 == b2 || *b1 == Base::Zero))
        })
    }

    pub fn equiv(&self, o: &Level) -> bool {
        self.leq(o) && o.leq(self)
    }

    pub fn is_zero(&self) -> bool {
        self.norm() == vec![(Base::Zero, 0)]
    }

    fn as_nat(&self) -> Option<u32> {
        match self {
            Level::Zero => Some(0),
            Level::Succ(l) => l.as_nat().map(|n| n + 1),
            _ => None,
        }
    }
}

fn simplify(v: Atoms) -> Atoms {
    let mut out: Atoms = Vec::new();
    for (b, k) in v {
        match out.iter_mut().find(|(b2, _)| *b2 == b) {
            Some(e) => e.1 = e.1.max(k),
            None => out.push((b, k)),
        }
    }
    if let Some(maxk) = out
        .iter()
        .filter(|(b, _)| *b != Base::Zero)
        .map(|(_, k)| *k)
        .max()
    {
        out.retain(|(b, k)| *b != Base::Zero || *k > maxk);
    }
    out.sort();
    out
}

fn from_atoms(v: &Atoms) -> Level {
    let mut it = v.iter().map(|(b, k)| {
        let base = match b {
            Base::Zero => Level::Zero,
            Base::Param(n) => Level::Param(n.clone()),
            Base::Stuck(l) => l.clone(),
        };
        (0..*k).fold(base, |l, _| l.succ())
    });
    let first = it.next().unwrap_or(Level::Zero);
    it.fold(first, Level::max)
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(n) = self.as_nat() {
            return write!(f, "{n}");
        }
        match self {
            Level::Succ(l) => write!(f, "{l}+1"),
            Level::Max(a, b) => write!(f, "max({a}, {b})"),
            Level::IMax(a, b) => write!(f, "imax({a}, {b})"),
            Level::Param(n) => write!(f, "{n}"),
            Level::Zero => write!(f, "0"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn comparisons() {
        let u = Level::param("u");
        let v = Level::param("v");
        assert!(Level::of_nat(1).leq(&Level::of_nat(2)));
        assert!(!Level::of_nat(2).leq(&Level::of_nat(1)));
        assert!(u.leq(&u.clone().succ()));
        assert!(!u.clone().succ().leq(&u));
        assert!(u.leq(&Level::max(u.clone(), v.clone())));
        assert!(Level::max(u.clone(), v.clone()).equiv(&Level::max(v.clone(), u.clone())));
        // imax(u, 0) = 0, imax(u, 1) = max(u, 1)
        assert!(Level::imax(u.clone(), Level::zero()).is_zero());
        assert!(Level::imax(u.clone(), Level::of_nat(1))
            .equiv(&Level::max(u.clone(), Level::of_nat(1))));
        // imax(u, v) is stuck: not equal to max(u, v)
        assert!(!Level::imax(u.clone(), v.clone()).equiv(&Level::max(u, v)));
    }
}
