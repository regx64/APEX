//! The global environment of checked declarations.

use crate::level::Level;
use crate::tc::TypeChecker;
use crate::term::*;
use std::collections::HashMap;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelError(pub String);

impl fmt::Display for KernelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for KernelError {}

pub type KResult<X> = Result<X, KernelError>;

pub fn kerr<X>(msg: impl Into<String>) -> KResult<X> {
    Err(KernelError(msg.into()))
}

#[derive(Clone)]
pub struct IndInfo {
    pub lparams: Vec<Name>,
    pub ty: T,
    pub nparams: usize,
    pub nindices: usize,
    pub ctors: Vec<Name>,
    pub is_prop: bool,
    pub rec: Name,
    /// All types of the mutual family this type belongs to, in declaration order.
    pub family: Vec<Name>,
}

#[derive(Clone)]
pub struct CtorInfo {
    pub lparams: Vec<Name>,
    pub ty: T,
    pub ind: Name,
    pub idx: usize,
    pub nparams: usize,
    pub nfields: usize,
}

#[derive(Clone)]
pub struct RecRule {
    pub ctor: Name,
    pub nfields: usize,
    /// `fun params motive minors fields => minor fields ihs`
    pub rhs: T,
}

#[derive(Clone)]
pub struct RecInfo {
    pub lparams: Vec<Name>,
    pub ty: T,
    pub ind: Name,
    pub nparams: usize,
    pub nindices: usize,
    /// Number of motives: one per type of the mutual family.
    pub nmotives: usize,
    /// Number of minor premises: one per constructor of the whole family.
    pub nminors: usize,
    pub rules: Vec<RecRule>,
}

#[derive(Clone)]
pub enum Decl {
    Axiom {
        lparams: Vec<Name>,
        ty: T,
    },
    Def {
        lparams: Vec<Name>,
        ty: T,
        val: T,
        height: u32,
    },
    Inductive(IndInfo),
    Ctor(CtorInfo),
    Rec(RecInfo),
}

impl Decl {
    pub fn lparams(&self) -> &[Name] {
        match self {
            Decl::Axiom { lparams, .. } | Decl::Def { lparams, .. } => lparams,
            Decl::Inductive(i) => &i.lparams,
            Decl::Ctor(c) => &c.lparams,
            Decl::Rec(r) => &r.lparams,
        }
    }

    pub fn ty(&self) -> &T {
        match self {
            Decl::Axiom { ty, .. } | Decl::Def { ty, .. } => ty,
            Decl::Inductive(i) => &i.ty,
            Decl::Ctor(c) => &c.ty,
            Decl::Rec(r) => &r.ty,
        }
    }
}

#[derive(Clone, Default)]
pub struct Env {
    decls: HashMap<Name, Decl>,
    counter: u32,
}

pub(crate) fn to_names(xs: &[&str]) -> Vec<Name> {
    xs.iter().map(|s| Name::from(*s)).collect()
}

fn check_level_params(t: &T, lps: &[Name]) -> KResult<()> {
    let mut used = Vec::new();
    collect_level_params(t, &mut used);
    match used.into_iter().find(|p| !lps.contains(p)) {
        Some(p) => kerr(format!("undeclared universe parameter `{p}`")),
        None => Ok(()),
    }
}

impl Env {
    pub fn new() -> Env {
        Env::default()
    }

    pub fn get(&self, name: &str) -> Option<&Decl> {
        self.decls.get(name)
    }

    pub(crate) fn insert(&mut self, name: Name, d: Decl) {
        self.decls.insert(name, d);
    }

    pub(crate) fn next_height(&mut self) -> u32 {
        self.counter += 1;
        self.counter
    }

    pub(crate) fn check_fresh(&self, name: &str) -> KResult<()> {
        if self.decls.contains_key(name) {
            kerr(format!("`{name}` is already declared"))
        } else {
            Ok(())
        }
    }

    pub(crate) fn check_decl_levels(&self, lps: &[Name], terms: &[&T]) -> KResult<()> {
        for (i, p) in lps.iter().enumerate() {
            if lps[..i].contains(p) {
                return kerr(format!("duplicate universe parameter `{p}`"));
            }
        }
        terms.iter().try_for_each(|t| check_level_params(t, lps))
    }

    pub fn add_axiom(&mut self, name: &str, lparams: &[&str], ty: T) -> KResult<()> {
        self.check_fresh(name)?;
        let lps = to_names(lparams);
        self.check_decl_levels(&lps, &[&ty])?;
        TypeChecker::new(self).check_is_type(&ty)?;
        self.insert(name.into(), Decl::Axiom { lparams: lps, ty });
        Ok(())
    }

    /// Add a definition (or theorem: a definition whose type is a proposition).
    /// Checks the type, the value's type, and the binder multiplicities.
    pub fn add_def(&mut self, name: &str, lparams: &[&str], ty: T, val: T) -> KResult<()> {
        self.check_fresh(name)?;
        let lps = to_names(lparams);
        self.check_decl_levels(&lps, &[&ty, &val])?;
        {
            let mut tc = TypeChecker::new(self);
            tc.check_is_type(&ty)?;
            let tv = tc.infer(&val)?;
            if !tc.is_def_eq(&tv, &ty)? {
                return kerr(format!(
                    "type mismatch in `{name}`: value has type {}, expected {}",
                    tc.pp(&tv),
                    tc.pp(&ty)
                ));
            }
            // proofs are erased at runtime: only data has to respect its multiplicities
            let is_proof = matches!(
                tc.infer(&ty).and_then(|s| tc.whnf(&s)).as_deref(),
                Ok(Term::Sort(l)) if l.is_zero()
            );
            if !is_proof {
                tc.check_mults(&val)?;
            }
        }
        let height = self.next_height();
        self.insert(
            name.into(),
            Decl::Def {
                lparams: lps,
                ty,
                val,
                height,
            },
        );
        Ok(())
    }

    /// Add a definition without checking its value: for proofs that were checked before
    /// (the library proof cache). The type is still checked; the caller vouches for `val`.
    pub fn add_def_trusted(&mut self, name: &str, lparams: &[&str], ty: T, val: T) -> KResult<()> {
        self.check_fresh(name)?;
        let lps = to_names(lparams);
        self.check_decl_levels(&lps, &[&ty, &val])?;
        TypeChecker::new(self).check_is_type(&ty)?;
        let height = self.next_height();
        self.insert(
            name.into(),
            Decl::Def {
                lparams: lps,
                ty,
                val,
                height,
            },
        );
        Ok(())
    }

    /// The type of `name` instantiated with universe levels `ls`.
    pub fn const_type(&self, name: &str, ls: &[Level]) -> KResult<T> {
        let d = match self.get(name) {
            Some(d) => d,
            None => return kerr(format!("unknown constant `{name}`")),
        };
        if d.lparams().len() != ls.len() {
            return kerr(format!(
                "`{name}` expects {} universe arguments, got {}",
                d.lparams().len(),
                ls.len()
            ));
        }
        Ok(instantiate_levels(d.ty(), d.lparams(), ls))
    }
}
