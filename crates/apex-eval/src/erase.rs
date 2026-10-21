//! Erasure: kernel terms to an untyped lambda IR.
//!
//! Types, proofs and arguments bound with multiplicity 0 become `Erased`.
//! Arity is preserved (an erased argument is still passed), so constructors
//! and recursors keep their logical argument positions.

use apex_kernel::term::*;
use apex_kernel::{Env, Mult, TypeChecker};
use std::rc::Rc;

#[derive(Debug)]
pub enum Ir {
    /// De Bruijn index into the runtime environment.
    Var(usize),
    Lam(Rc<Ir>),
    App(Rc<Ir>, Rc<Ir>),
    Global(Rc<str>),
    Erased,
    Nat(u128),
    Str(Rc<str>),
    /// `let` binding: value, then body (which sees the new variable at index 0).
    Let(Rc<Ir>, Rc<Ir>),
}

pub struct Eraser<'a> {
    tc: TypeChecker<'a>,
    stack: Vec<u32>,
}

type R<X> = Result<X, String>;

impl<'a> Eraser<'a> {
    pub fn new(env: &'a Env) -> Self {
        Eraser {
            tc: TypeChecker::new(env),
            stack: Vec::new(),
        }
    }

    /// Erase a closed kernel term.
    pub fn erase_closed(&mut self, t: &T) -> R<Rc<Ir>> {
        self.stack.clear();
        self.erase(t)
    }

    /// Is `t` a type or a proof (and so has no runtime content)?
    fn is_erased(&mut self, t: &T) -> R<bool> {
        let ty = self.tc.infer(t).map_err(|e| e.0)?;
        let w = self.tc.whnf(&ty).map_err(|e| e.0)?;
        if matches!(&*w, Term::Sort(_)) {
            return Ok(true);
        }
        let s = self.tc.infer(&ty).map_err(|e| e.0)?;
        let s = self.tc.whnf(&s).map_err(|e| e.0)?;
        Ok(matches!(&*s, Term::Sort(l) if l.is_zero()))
    }

    fn erase(&mut self, t: &T) -> R<Rc<Ir>> {
        if self.is_erased(t)? {
            return Ok(Rc::new(Ir::Erased));
        }
        Ok(Rc::new(match &**t {
            Term::FVar(id) => match self.stack.iter().rposition(|x| x == id) {
                Some(p) => Ir::Var(self.stack.len() - 1 - p),
                None => return Err("internal error: free variable outside its binder".into()),
            },
            Term::Const(n, _) => Ir::Global(n.clone()),
            Term::Lit(n) => Ir::Nat(*n),
            Term::Str(s) => Ir::Str(s.clone()),
            Term::App(f, a) => {
                let tf = self.tc.infer(f).map_err(|e| e.0)?;
                let tf = self.tc.whnf(&tf).map_err(|e| e.0)?;
                let m = match &*tf {
                    Term::Pi(m, ..) => *m,
                    _ => return Err("internal error: application of a non-function".into()),
                };
                let fe = self.erase(f)?;
                let ae = if m == Mult::Zero {
                    Rc::new(Ir::Erased)
                } else {
                    self.erase(a)?
                };
                Ir::App(fe, ae)
            }
            Term::Lam(m, d, b) => {
                let x = self.tc.fresh("x", d.clone(), *m);
                self.stack.push(x);
                let body = self.erase(&instantiate(b, &fvar(x)));
                self.stack.pop();
                Ir::Lam(body?)
            }
            Term::Let(m, ty, v, b) => {
                let val = if *m == Mult::Zero {
                    Rc::new(Ir::Erased)
                } else {
                    self.erase(v)?
                };
                let x = self.tc.fresh("x", ty.clone(), *m);
                self.stack.push(x);
                let body = self.erase(&instantiate(b, &fvar(x)));
                self.stack.pop();
                Ir::Let(val, body?)
            }
            Term::Sort(_) | Term::Pi(..) => Ir::Erased,
            Term::BVar(_) | Term::MVar(_) => {
                return Err("internal error: unexpected variable in kernel term".into())
            }
        }))
    }
}
