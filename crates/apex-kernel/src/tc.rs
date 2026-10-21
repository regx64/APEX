//! Type inference, reduction and definitional equality.

use crate::env::{kerr, Decl, Env, KResult};
use crate::level::Level;
use crate::term::*;
use std::collections::HashMap;

pub struct Local {
    pub name: Name,
    pub ty: T,
    pub mult: Mult,
}

pub struct TypeChecker<'a> {
    env: &'a Env,
    lctx: HashMap<u32, Local>,
    next: u32,
    /// Metavariable state. Only the elaborator creates metavariables; a fresh
    /// checker (as used for the final kernel check) rejects any `MVar`.
    mvar_types: HashMap<u32, T>,
    mvar_assign: HashMap<u32, T>,
    level_assign: HashMap<u32, Level>,
    next_mvar: u32,
}

/// Saved assignment state, for backtracking a failed unification attempt.
pub struct Snapshot {
    mvar_assign: HashMap<u32, T>,
    level_assign: HashMap<u32, Level>,
}

impl<'a> TypeChecker<'a> {
    pub fn new(env: &'a Env) -> Self {
        TypeChecker {
            env,
            lctx: HashMap::new(),
            next: 0,
            mvar_types: HashMap::new(),
            mvar_assign: HashMap::new(),
            level_assign: HashMap::new(),
            next_mvar: 0,
        }
    }

    // ---- metavariables ----

    pub fn new_mvar(&mut self, ty: T) -> T {
        let id = self.next_mvar;
        self.next_mvar += 1;
        self.mvar_types.insert(id, ty);
        mvar(id)
    }

    pub fn new_level_mvar(&mut self) -> Level {
        let id = self.next_mvar;
        self.next_mvar += 1;
        Level::MVar(id)
    }

    pub fn snapshot(&self) -> Snapshot {
        Snapshot {
            mvar_assign: self.mvar_assign.clone(),
            level_assign: self.level_assign.clone(),
        }
    }

    pub fn restore(&mut self, s: Snapshot) {
        self.mvar_assign = s.mvar_assign;
        self.level_assign = s.level_assign;
    }

    /// Substitute assigned metavariables (term and level), beta-reducing
    /// instantiated heads.
    pub fn zonk(&self, t: &T) -> T {
        match &**t {
            Term::MVar(id) => match self.mvar_assign.get(id) {
                Some(v) => self.zonk(v),
                None => t.clone(),
            },
            Term::Sort(l) => sort(l.subst_mvars(&self.level_assign)),
            Term::Const(n, ls) => cnst(
                n.clone(),
                ls.iter()
                    .map(|l| l.subst_mvars(&self.level_assign))
                    .collect(),
            ),
            Term::App(..) => {
                let (f, args) = app_spine(t);
                let head_is_mvar = matches!(&*f, Term::MVar(_));
                let r = mk_apps(
                    &self.zonk(&f),
                    &args.iter().map(|a| self.zonk(a)).collect::<Vec<_>>(),
                );
                if head_is_mvar {
                    head_beta(&r)
                } else {
                    r
                }
            }
            Term::Lam(m, ty, b) => lam(*m, self.zonk(ty), self.zonk(b)),
            Term::Pi(m, ty, b) => pi(*m, self.zonk(ty), self.zonk(b)),
            Term::Let(m, ty, v, b) => let_(*m, self.zonk(ty), self.zonk(v), self.zonk(b)),
            Term::BVar(_) | Term::FVar(_) | Term::Lit(_) | Term::Str(_) => t.clone(),
        }
    }

    pub fn zonk_level(&self, l: &Level) -> Level {
        l.subst_mvars(&self.level_assign)
    }

    /// Zonk the recorded types of all local variables.
    pub fn zonk_locals(&mut self) {
        let ids: Vec<u32> = self.lctx.keys().copied().collect();
        for id in ids {
            let ty = self.zonk(&self.lctx[&id].ty);
            if let Some(l) = self.lctx.get_mut(&id) {
                l.ty = ty;
            }
        }
    }

    fn level_eq(&mut self, a: &Level, b: &Level) -> bool {
        let a = a.subst_mvars(&self.level_assign);
        let b = b.subst_mvars(&self.level_assign);
        if a.equiv(&b) {
            return true;
        }
        match (&a, &b) {
            (Level::MVar(m), _) if !b.contains_mvar(*m) => {
                self.level_assign.insert(*m, b);
                true
            }
            (_, Level::MVar(m)) if !a.contains_mvar(*m) => {
                self.level_assign.insert(*m, a);
                true
            }
            (Level::Succ(x), Level::Succ(y)) => self.level_eq(x, y),
            _ => false,
        }
    }

    fn levels_eq(&mut self, a: &[Level], b: &[Level]) -> bool {
        a.len() == b.len() && a.iter().zip(b).all(|(x, y)| self.level_eq(x, y))
    }

    /// Unify a metavariable-headed side with the other side (Miller patterns).
    fn try_assign(&mut self, a: &T, b: &T) -> KResult<Option<bool>> {
        for (x, y) in [(a, b), (b, a)] {
            let (h, args) = app_spine(x);
            let m = match &*h {
                Term::MVar(m) => *m,
                _ => continue,
            };
            let (h2, _) = app_spine(y);
            if matches!(&*h2, Term::MVar(m2) if *m2 == m) {
                return Ok(None);
            }
            let mut fvs: Vec<u32> = Vec::new();
            let mut pattern = true;
            for arg in &args {
                match &**arg {
                    Term::FVar(i) if !fvs.contains(i) => fvs.push(*i),
                    _ => pattern = false,
                }
            }
            if !pattern {
                continue;
            }
            let rhs = self.zonk(y);
            if contains_mvar_id(&rhs, m) {
                return Ok(Some(false));
            }
            if args.is_empty() {
                let Ok(tv) = self.infer(&rhs) else {
                    return Ok(Some(false));
                };
                let mt = self.mvar_types[&m].clone();
                if !self.is_def_eq(&tv, &mt)? {
                    return Ok(Some(false));
                }
            }
            let val = if fvs.is_empty() {
                rhs
            } else {
                self.mk_lam(&fvs, &rhs)
            };
            self.mvar_assign.insert(m, val);
            return Ok(Some(true));
        }
        Ok(None)
    }

    // ---- local context ----

    pub fn fresh(&mut self, name: &str, ty: T, mult: Mult) -> u32 {
        let id = self.next;
        self.next += 1;
        self.lctx.insert(
            id,
            Local {
                name: name.into(),
                ty,
                mult,
            },
        );
        id
    }

    /// Replace the recorded type of a local with a definitionally equal one.
    pub fn set_local_ty(&mut self, id: u32, ty: T) {
        if let Some(l) = self.lctx.get_mut(&id) {
            l.ty = ty;
        }
    }

    pub fn local_mult(&self, id: u32) -> Option<Mult> {
        self.lctx.get(&id).map(|l| l.mult)
    }

    pub fn local_ty(&self, id: u32) -> KResult<T> {
        match self.lctx.get(&id) {
            Some(l) => Ok(l.ty.clone()),
            None => kerr(format!("unknown free variable _f{id}")),
        }
    }

    pub fn pp(&self, t: &T) -> String {
        let s = fmt_term(t, &|i| match self.lctx.get(&i) {
            Some(l) => l.name.to_string(),
            None => format!("_f{i}"),
        });
        // the printer parenthesizes every compound term; drop the outermost pair
        let compound = matches!(
            &**t,
            Term::App(..) | Term::Pi(..) | Term::Lam(..) | Term::Let(..)
        );
        if compound && s.starts_with('(') && s.ends_with(')') {
            s[1..s.len() - 1].to_string()
        } else {
            s
        }
    }

    /// Close `body` over `fvars` (outermost first), producing nested Π or λ.
    pub fn mk_binding(&self, fvars: &[u32], body: &T, is_pi: bool) -> T {
        let mut r = abstract_fvars(body, fvars);
        for i in (0..fvars.len()).rev() {
            let l = &self.lctx[&fvars[i]];
            let ty = abstract_fvars(&l.ty, &fvars[..i]);
            r = if is_pi {
                pi(l.mult, ty, r)
            } else {
                lam(l.mult, ty, r)
            };
        }
        r
    }

    pub fn mk_pi(&self, fvars: &[u32], body: &T) -> T {
        self.mk_binding(fvars, body, true)
    }

    pub fn mk_lam(&self, fvars: &[u32], body: &T) -> T {
        self.mk_binding(fvars, body, false)
    }

    /// Open up to `limit` (default: all) leading Π binders into fresh locals.
    pub fn telescope(&mut self, ty: &T, limit: Option<usize>) -> KResult<(Vec<u32>, T)> {
        let mut fvs = Vec::new();
        let mut cur = ty.clone();
        loop {
            if Some(fvs.len()) == limit {
                break;
            }
            let w = match &*cur {
                Term::Pi(..) => cur.clone(),
                _ => self.whnf(&cur)?,
            };
            match &*w {
                Term::Pi(m, d, b) => {
                    let id = self.fresh("a", d.clone(), *m);
                    cur = instantiate(b, &fvar(id));
                    fvs.push(id);
                }
                _ => {
                    cur = w;
                    break;
                }
            }
        }
        if let Some(n) = limit {
            if fvs.len() < n {
                return kerr(format!("expected at least {n} binders in {}", self.pp(ty)));
            }
        }
        Ok((fvs, cur))
    }

    /// Apply the leading Π binders of `ty` to `vals`, checking argument types.
    pub fn instantiate_pis(&mut self, ty: &T, vals: &[T]) -> KResult<T> {
        let mut cur = ty.clone();
        for v in vals {
            let w = self.whnf(&cur)?;
            match &*w {
                Term::Pi(_, d, b) => {
                    let tv = self.infer(v)?;
                    if !self.is_def_eq(&tv, d)? {
                        return kerr(format!(
                            "parameter mismatch: {} does not have type {}",
                            self.pp(v),
                            self.pp(d)
                        ));
                    }
                    cur = instantiate(b, v);
                }
                _ => return kerr("too many parameters"),
            }
        }
        Ok(cur)
    }

    // ---- inference ----

    pub fn infer(&mut self, t: &T) -> KResult<T> {
        match &**t {
            Term::BVar(_) => kerr("loose bound variable"),
            Term::MVar(id) => match self.mvar_types.get(id) {
                Some(t) => Ok(t.clone()),
                None => kerr("metavariable in kernel term"),
            },
            Term::FVar(id) => self.local_ty(*id),
            Term::Sort(l) => Ok(sort(l.clone().succ())),
            Term::Lit(_) => Ok(cnst("Nat".into(), vec![])),
            Term::Str(_) => Ok(cnst("String".into(), vec![])),
            Term::Const(n, ls) => self.env.const_type(n, ls),
            Term::App(f, a) => {
                let tf = self.infer(f)?;
                let tf = self.whnf(&tf)?;
                match &*tf {
                    Term::Pi(_, d, b) => {
                        let ta = self.infer(a)?;
                        if !self.is_def_eq(&ta, d)? {
                            return kerr(format!(
                                "application type mismatch: argument {} has type {}, expected {}",
                                self.pp(a),
                                self.pp(&ta),
                                self.pp(d)
                            ));
                        }
                        Ok(instantiate(b, a))
                    }
                    _ => kerr(format!(
                        "function expected, got {} : {}",
                        self.pp(f),
                        self.pp(&tf)
                    )),
                }
            }
            Term::Lam(m, d, b) => {
                self.check_is_type(d)?;
                let x = self.fresh("x", d.clone(), *m);
                let tb = self.infer(&instantiate(b, &fvar(x)))?;
                Ok(pi(*m, d.clone(), abstract_fvars(&tb, &[x])))
            }
            Term::Pi(m, d, b) => {
                let l1 = self.check_is_type(d)?;
                let x = self.fresh("x", d.clone(), *m);
                let l2 = self.check_is_type(&instantiate(b, &fvar(x)))?;
                Ok(sort(Level::imax(l1, l2)))
            }
            Term::Let(_, ty, v, b) => {
                self.check_is_type(ty)?;
                let tv = self.infer(v)?;
                if !self.is_def_eq(&tv, ty)? {
                    return kerr(format!(
                        "let value {} does not have type {}",
                        self.pp(v),
                        self.pp(ty)
                    ));
                }
                self.infer(&instantiate(b, v))
            }
        }
    }

    pub fn ensure_sort(&mut self, t: &T) -> KResult<Level> {
        let w = self.whnf(t)?;
        match &*w {
            Term::Sort(l) => Ok(l.clone()),
            _ => kerr(format!("type expected, got {}", self.pp(t))),
        }
    }

    /// Check that `t` is a type and return the universe it lives in.
    pub fn check_is_type(&mut self, t: &T) -> KResult<Level> {
        let ty = self.infer(t)?;
        self.ensure_sort(&ty)
    }

    // ---- reduction ----

    fn unfold(&self, t: &T) -> Option<T> {
        let (f, args) = app_spine(t);
        if let Term::Const(n, ls) = &*f {
            if let Some(Decl::Def { lparams, val, .. }) = self.env.get(n) {
                if lparams.len() == ls.len() {
                    return Some(mk_apps(&instantiate_levels(val, lparams, ls), &args));
                }
            }
        }
        None
    }

    fn def_height(&self, t: &T) -> Option<(Name, u32)> {
        let (f, _) = app_spine(t);
        if let Term::Const(n, ls) = &*f {
            if let Some(Decl::Def {
                lparams, height, ..
            }) = self.env.get(n)
            {
                if lparams.len() == ls.len() {
                    return Some((n.clone(), *height));
                }
            }
        }
        None
    }

    /// `Nat.add` / `Nat.mul` on two literals compute directly.
    fn reduce_nat_op(&mut self, f: &T, args: &[T]) -> KResult<Option<T>> {
        let Term::Const(n, _) = &**f else {
            return Ok(None);
        };
        if args.len() != 2 || !matches!(&**n, "Nat.add" | "Nat.mul") {
            return Ok(None);
        }
        let a = self.whnf(&args[0])?;
        let b = self.whnf(&args[1])?;
        let (Term::Lit(x), Term::Lit(y)) = (&*a, &*b) else {
            return Ok(None);
        };
        let r = if &**n == "Nat.add" {
            x.checked_add(*y)
        } else {
            x.checked_mul(*y)
        };
        Ok(r.map(lit))
    }

    /// ι-reduction: `I.rec ... (c fields)` ⟶ minor premise applied to the fields.
    fn reduce_rec(&mut self, f: &T, args: &[T]) -> KResult<Option<T>> {
        let (n, ls) = match &**f {
            Term::Const(n, ls) => (n, ls),
            _ => return Ok(None),
        };
        let env = self.env;
        let r = match env.get(n) {
            Some(Decl::Rec(r)) => r,
            _ => return Ok(None),
        };
        let major_idx = r.nparams + r.nmotives + r.nminors + r.nindices;
        if args.len() <= major_idx || r.lparams.len() != ls.len() {
            return Ok(None);
        }
        let mut major = self.whnf(&args[major_idx])?;
        if let Term::Lit(n) = &*major {
            major = lit_to_ctor(*n);
        }
        let (mh, margs) = app_spine(&major);
        let cname = match &*mh {
            Term::Const(c, _) => c,
            _ => return Ok(None),
        };
        let rule = match r.rules.iter().find(|ru| ru.ctor == *cname) {
            Some(ru) => ru,
            None => return Ok(None),
        };
        let nparams = match env.get(cname) {
            Some(Decl::Ctor(ci)) => ci.nparams,
            _ => return Ok(None),
        };
        if margs.len() != nparams + rule.nfields {
            return Ok(None);
        }
        let rhs = instantiate_levels(&rule.rhs, &r.lparams, ls);
        let mut res = mk_apps(&rhs, &args[..r.nparams + r.nmotives + r.nminors]);
        res = mk_apps(&res, &margs[nparams..]);
        res = mk_apps(&res, &args[major_idx + 1..]);
        Ok(Some(res))
    }

    /// β, ζ and ι reduction to weak head normal form (no δ).
    pub fn whnf_core(&mut self, t: &T) -> KResult<T> {
        let mut cur = t.clone();
        loop {
            match &*cur.clone() {
                Term::MVar(id) => match self.mvar_assign.get(id) {
                    Some(v) => cur = v.clone(),
                    None => return Ok(cur),
                },
                Term::Let(_, _, v, b) => cur = instantiate(b, v),
                Term::App(..) => {
                    let (f, args) = app_spine(&cur);
                    let f2 = self.whnf_core(&f)?;
                    match &*f2 {
                        Term::Lam(..) => {
                            let mut body = f2.clone();
                            let mut i = 0;
                            while i < args.len() {
                                let next = match &*body {
                                    Term::Lam(_, _, b) => instantiate(b, &args[i]),
                                    _ => break,
                                };
                                body = next;
                                i += 1;
                            }
                            cur = mk_apps(&body, &args[i..]);
                        }
                        Term::Const(..) => match self
                            .reduce_nat_op(&f2, &args)?
                            .map_or_else(|| self.reduce_rec(&f2, &args), |r| Ok(Some(r)))?
                        {
                            Some(r) => cur = r,
                            None => return Ok(if f == f2 { cur } else { mk_apps(&f2, &args) }),
                        },
                        _ => return Ok(if f == f2 { cur } else { mk_apps(&f2, &args) }),
                    }
                }
                _ => return Ok(cur),
            }
        }
    }

    pub fn whnf(&mut self, t: &T) -> KResult<T> {
        let mut cur = t.clone();
        loop {
            cur = self.whnf_core(&cur)?;
            match self.unfold(&cur) {
                Some(n) => cur = n,
                None => return Ok(cur),
            }
        }
    }

    // ---- definitional equality ----

    pub fn is_def_eq(&mut self, a: &T, b: &T) -> KResult<bool> {
        if a == b {
            return Ok(true);
        }
        let a = self.whnf_core(a)?;
        let b = self.whnf_core(b)?;
        if a == b {
            return Ok(true);
        }
        if let Some(r) = self.try_assign(&a, &b)? {
            return Ok(r);
        }
        match (&*a, &*b) {
            (Term::Lit(x), Term::Lit(y)) => return Ok(x == y),
            (Term::Lit(n), _) => {
                if let Some(r) = self.lit_vs(*n, &b)? {
                    return Ok(r);
                }
            }
            (_, Term::Lit(n)) => {
                if let Some(r) = self.lit_vs(*n, &a)? {
                    return Ok(r);
                }
            }
            _ => {}
        }
        match (&*a, &*b) {
            (Term::Sort(l1), Term::Sort(l2)) => return Ok(self.level_eq(l1, l2)),
            (Term::Pi(m1, d1, b1), Term::Pi(m2, d2, b2))
            | (Term::Lam(m1, d1, b1), Term::Lam(m2, d2, b2)) => {
                if m1 != m2 || !self.is_def_eq(d1, d2)? {
                    return Ok(false);
                }
                let x = fvar(self.fresh("x", d1.clone(), *m1));
                return self.is_def_eq(&instantiate(b1, &x), &instantiate(b2, &x));
            }
            // η: `fun x => f x` ≡ `f`
            (Term::Lam(m, d, body), _) => {
                let x = fvar(self.fresh("x", d.clone(), *m));
                return self.is_def_eq(&instantiate(body, &x), &app(b.clone(), x));
            }
            (_, Term::Lam(m, d, body)) => {
                let x = fvar(self.fresh("x", d.clone(), *m));
                return self.is_def_eq(&app(a.clone(), x.clone()), &instantiate(body, &x));
            }
            _ => {}
        }
        // lazy δ-reduction: unfold the most recently defined constant first
        match (self.def_height(&a), self.def_height(&b)) {
            (None, None) => {}
            (Some(_), None) => {
                let ua = self.unfold(&a).expect("def_height implies unfoldable");
                return self.is_def_eq(&ua, &b);
            }
            (None, Some(_)) => {
                let ub = self.unfold(&b).expect("def_height implies unfoldable");
                return self.is_def_eq(&a, &ub);
            }
            (Some((na, ha)), Some((nb, hb))) => {
                if na == nb && self.spine_def_eq(&a, &b)? {
                    return Ok(true);
                }
                let ua = self.unfold(&a).expect("unfoldable");
                let ub = self.unfold(&b).expect("unfoldable");
                return match ha.cmp(&hb) {
                    std::cmp::Ordering::Greater => self.is_def_eq(&ua, &b),
                    std::cmp::Ordering::Less => self.is_def_eq(&a, &ub),
                    std::cmp::Ordering::Equal => self.is_def_eq(&ua, &ub),
                };
            }
        }
        if self.spine_def_eq(&a, &b)? {
            return Ok(true);
        }
        self.proof_irrelevant(&a, &b)
    }

    /// Compare literal `n` with `Nat.zero` or `Nat.succ x`; `None` if `other` is neither.
    fn lit_vs(&mut self, n: u64, other: &T) -> KResult<Option<bool>> {
        let (h, args) = app_spine(other);
        match (&*h, args.len()) {
            (Term::Const(c, _), 0) if &**c == "Nat.zero" => Ok(Some(n == 0)),
            (Term::Const(c, _), 1) if &**c == "Nat.succ" => {
                if n == 0 {
                    Ok(Some(false))
                } else {
                    Ok(Some(self.is_def_eq(&lit(n - 1), &args[0])?))
                }
            }
            _ => Ok(None),
        }
    }

    fn spine_def_eq(&mut self, a: &T, b: &T) -> KResult<bool> {
        let (fa, aa) = app_spine(a);
        let (fb, ab) = app_spine(b);
        if aa.len() != ab.len() {
            return Ok(false);
        }
        let same_head = match (&*fa, &*fb) {
            (Term::Const(n1, l1), Term::Const(n2, l2)) => n1 == n2 && self.levels_eq(l1, l2),
            (Term::FVar(i), Term::FVar(j)) => i == j,
            (Term::MVar(i), Term::MVar(j)) => i == j,
            _ => false,
        };
        if !same_head {
            return Ok(false);
        }
        for (x, y) in aa.iter().zip(&ab) {
            if !self.is_def_eq(x, y)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Any two proofs of the same proposition are equal.
    fn proof_irrelevant(&mut self, a: &T, b: &T) -> KResult<bool> {
        let ta = match self.infer(a) {
            Ok(t) => t,
            Err(_) => return Ok(false),
        };
        let is_proof = match self.infer(&ta).and_then(|s| self.ensure_sort(&s)) {
            Ok(l) => l.is_zero(),
            Err(_) => false,
        };
        if !is_proof {
            return Ok(false);
        }
        match self.infer(b) {
            Ok(tb) => self.is_def_eq(&ta, &tb),
            Err(_) => Ok(false),
        }
    }

    // ---- quantitative checks ----

    /// How many times `x` is used at runtime in `t` (types and erased
    /// arguments do not count).
    pub fn usage(&mut self, t: &T, x: u32) -> KResult<Mult> {
        match &**t {
            Term::FVar(y) => Ok(if *y == x { Mult::One } else { Mult::Zero }),
            Term::BVar(_)
            | Term::MVar(_)
            | Term::Sort(_)
            | Term::Pi(..)
            | Term::Const(..)
            | Term::Lit(_)
            | Term::Str(_) => Ok(Mult::Zero),
            Term::App(..) => {
                // walk the whole application spine at once: one `infer` of the head,
                // then peel the Π binders to learn each argument's multiplicity
                let (f, args) = app_spine(t);
                let mut total = self.usage(&f, x)?;
                let mut ty = self.infer(&f)?;
                for a in &args {
                    ty = self.whnf(&ty)?;
                    let (m, body) = match &*ty {
                        Term::Pi(m, _, b) => (*m, b.clone()),
                        _ => return kerr(format!("function expected, got {}", self.pp(&f))),
                    };
                    let ua = if m == Mult::Zero {
                        Mult::Zero
                    } else {
                        self.usage(a, x)?
                    };
                    total = total.plus(m.times(ua));
                    ty = instantiate(&body, a);
                }
                Ok(total)
            }
            Term::Lam(m, d, b) => {
                let y = self.fresh("y", d.clone(), *m);
                self.usage(&instantiate(b, &fvar(y)), x)
            }
            Term::Let(m, ty, v, b) => {
                let y = self.fresh("y", ty.clone(), *m);
                let uv = self.usage(v, x)?;
                let ub = self.usage(&instantiate(b, &fvar(y)), x)?;
                Ok(m.times(uv).plus(ub))
            }
        }
    }

    fn check_binder_usage(&mut self, m: Mult, body: &T, x: u32) -> KResult<()> {
        if m == Mult::Omega {
            return Ok(()); // unrestricted: any use is fine
        }
        let u = self.usage(body, x)?;
        if u == m {
            Ok(())
        } else {
            kerr(format!(
                "multiplicity violation: variable bound with {m:?} is used {u:?} at runtime"
            ))
        }
    }

    /// Verify every binder in the runtime-relevant part of `t` is used
    /// according to its multiplicity.
    pub fn check_mults(&mut self, t: &T) -> KResult<()> {
        match &**t {
            Term::Lam(m, d, b) => {
                let x = self.fresh("x", d.clone(), *m);
                let body = instantiate(b, &fvar(x));
                self.check_mults(&body)?;
                self.check_binder_usage(*m, &body, x)
            }
            Term::App(..) => {
                let (f, args) = app_spine(t);
                self.check_mults(&f)?;
                let mut ty = self.infer(&f)?;
                for a in &args {
                    ty = self.whnf(&ty)?;
                    let (m, body) = match &*ty {
                        Term::Pi(m, _, b) => (*m, b.clone()),
                        _ => return kerr(format!("function expected, got {}", self.pp(&f))),
                    };
                    if m != Mult::Zero {
                        self.check_mults(a)?;
                    }
                    ty = instantiate(&body, a);
                }
                Ok(())
            }
            Term::Let(m, ty, v, b) => {
                self.check_mults(v)?;
                let x = self.fresh("x", ty.clone(), *m);
                let body = instantiate(b, &fvar(x));
                self.check_mults(&body)?;
                self.check_binder_usage(*m, &body, x)
            }
            _ => Ok(()),
        }
    }
}

fn lit_to_ctor(n: u64) -> T {
    if n == 0 {
        cnst("Nat.zero".into(), vec![])
    } else {
        app(cnst("Nat.succ".into(), vec![]), lit(n - 1))
    }
}
