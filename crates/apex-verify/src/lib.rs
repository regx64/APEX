//! An independent checker for exported APEX declarations.
//!
//! It shares **no code** with `apex-kernel`: it reads the export format (`Env::export`),
//! has its own term representation and its own type checker (weak-head reduction, definitional
//! equality, inference), and re-checks every definition and theorem from scratch. A bug in the
//! kernel that lets a wrong proof through would have to be repeated here to go unnoticed.
//!
//! What is checked: every axiom's and definition's *type* is a type; every definition's value
//! has its stated type. Inductive types, constructors and recursors (with their reduction
//! rules) are taken as given, but their types and rule right-hand sides must be well-typed:
//! the verifier does not re-derive recursors from the inductive declaration, so it trusts
//! the kernel's inductive-types module. Quantity annotations (0/1/ω binders) are ignored: they
//! constrain runtime resources, not truth.

use std::collections::HashMap;
use std::rc::Rc;

// ---------------------------------------------------------------- terms

type Name = Rc<str>;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Lvl {
    Zero,
    Succ(Rc<Lvl>),
    Max(Rc<Lvl>, Rc<Lvl>),
    IMax(Rc<Lvl>, Rc<Lvl>),
    Param(Name),
}

type Tm = Rc<Term>;

#[derive(Debug, PartialEq, Eq)]
enum Term {
    BVar(u32),
    FVar(u32),
    Sort(Lvl),
    Const(Name, Vec<Lvl>),
    Lit(u128),
    Str(Name),
    App(Tm, Tm),
    Lam(Tm, Tm),
    Pi(Tm, Tm),
    Let(Tm, Tm, Tm),
}

use Term::*;

fn app(f: Tm, a: Tm) -> Tm {
    Rc::new(App(f, a))
}

fn apps(f: &Tm, args: &[Tm]) -> Tm {
    args.iter().fold(f.clone(), |acc, a| app(acc, a.clone()))
}

fn spine(t: &Tm) -> (Tm, Vec<Tm>) {
    let mut args = Vec::new();
    let mut cur = t.clone();
    while let App(f, a) = &*cur.clone() {
        args.push(a.clone());
        cur = f.clone();
    }
    args.reverse();
    (cur, args)
}

/// Replace the loose bound variable `k` (counting binders passed) by `v`.
fn subst(t: &Tm, v: &Tm, k: u32) -> Tm {
    match &**t {
        BVar(i) => {
            if *i == k {
                lift(v, k)
            } else if *i > k {
                Rc::new(BVar(i - 1))
            } else {
                t.clone()
            }
        }
        App(f, a) => app(subst(f, v, k), subst(a, v, k)),
        Lam(d, b) => Rc::new(Lam(subst(d, v, k), subst(b, v, k + 1))),
        Pi(d, b) => Rc::new(Pi(subst(d, v, k), subst(b, v, k + 1))),
        Let(d, x, b) => Rc::new(Let(subst(d, v, k), subst(x, v, k), subst(b, v, k + 1))),
        _ => t.clone(),
    }
}

/// Shift the loose bound variables of `t` up by `n`.
fn lift(t: &Tm, n: u32) -> Tm {
    if n == 0 {
        return t.clone();
    }
    fn go(t: &Tm, n: u32, cut: u32) -> Tm {
        match &**t {
            BVar(i) if *i >= cut => Rc::new(BVar(i + n)),
            App(f, a) => app(go(f, n, cut), go(a, n, cut)),
            Lam(d, b) => Rc::new(Lam(go(d, n, cut), go(b, n, cut + 1))),
            Pi(d, b) => Rc::new(Pi(go(d, n, cut), go(b, n, cut + 1))),
            Let(d, x, b) => Rc::new(Let(go(d, n, cut), go(x, n, cut), go(b, n, cut + 1))),
            _ => t.clone(),
        }
    }
    go(t, n, 0)
}

fn inst(body: &Tm, v: &Tm) -> Tm {
    subst(body, v, 0)
}

/// Replace the free variable `id` by the bound variable `k` (for building binders).
fn abstract_fv(t: &Tm, id: u32, k: u32) -> Tm {
    match &**t {
        FVar(j) if *j == id => Rc::new(BVar(k)),
        App(f, a) => app(abstract_fv(f, id, k), abstract_fv(a, id, k)),
        Lam(d, b) => Rc::new(Lam(abstract_fv(d, id, k), abstract_fv(b, id, k + 1))),
        Pi(d, b) => Rc::new(Pi(abstract_fv(d, id, k), abstract_fv(b, id, k + 1))),
        Let(d, x, b) => Rc::new(Let(
            abstract_fv(d, id, k),
            abstract_fv(x, id, k),
            abstract_fv(b, id, k + 1),
        )),
        _ => t.clone(),
    }
}

fn has_fvar(t: &Tm, id: u32) -> bool {
    match &**t {
        FVar(j) => *j == id,
        App(f, a) => has_fvar(f, id) || has_fvar(a, id),
        Lam(d, b) | Pi(d, b) => has_fvar(d, id) || has_fvar(b, id),
        Let(d, x, b) => has_fvar(d, id) || has_fvar(x, id) || has_fvar(b, id),
        _ => false,
    }
}

fn inst_lvls(t: &Tm, ps: &[Name], ls: &[Lvl]) -> Tm {
    if ps.is_empty() {
        return t.clone();
    }
    match &**t {
        Sort(l) => Rc::new(Sort(l_inst(l, ps, ls))),
        Const(n, lv) => Rc::new(Const(
            n.clone(),
            lv.iter().map(|l| l_inst(l, ps, ls)).collect(),
        )),
        App(f, a) => app(inst_lvls(f, ps, ls), inst_lvls(a, ps, ls)),
        Lam(d, b) => Rc::new(Lam(inst_lvls(d, ps, ls), inst_lvls(b, ps, ls))),
        Pi(d, b) => Rc::new(Pi(inst_lvls(d, ps, ls), inst_lvls(b, ps, ls))),
        Let(d, x, b) => Rc::new(Let(
            inst_lvls(d, ps, ls),
            inst_lvls(x, ps, ls),
            inst_lvls(b, ps, ls),
        )),
        _ => t.clone(),
    }
}

// ---------------------------------------------------------------- levels

fn l_inst(l: &Lvl, ps: &[Name], ls: &[Lvl]) -> Lvl {
    match l {
        Lvl::Zero => Lvl::Zero,
        Lvl::Succ(a) => Lvl::Succ(Rc::new(l_inst(a, ps, ls))),
        Lvl::Max(a, b) => Lvl::Max(Rc::new(l_inst(a, ps, ls)), Rc::new(l_inst(b, ps, ls))),
        Lvl::IMax(a, b) => Lvl::IMax(Rc::new(l_inst(a, ps, ls)), Rc::new(l_inst(b, ps, ls))),
        Lvl::Param(n) => match ps.iter().position(|p| p == n) {
            Some(i) => ls.get(i).cloned().unwrap_or_else(|| l.clone()),
            None => l.clone(),
        },
    }
}

fn l_params(l: &Lvl, out: &mut Vec<Name>) {
    match l {
        Lvl::Zero => {}
        Lvl::Succ(a) => l_params(a, out),
        Lvl::Max(a, b) | Lvl::IMax(a, b) => {
            l_params(a, out);
            l_params(b, out);
        }
        Lvl::Param(n) => {
            if !out.contains(n) {
                out.push(n.clone())
            }
        }
    }
}

fn l_eval(l: &Lvl, env: &HashMap<Name, u32>) -> u32 {
    match l {
        Lvl::Zero => 0,
        Lvl::Succ(a) => l_eval(a, env) + 1,
        Lvl::Max(a, b) => l_eval(a, env).max(l_eval(b, env)),
        Lvl::IMax(a, b) => {
            let y = l_eval(b, env);
            if y == 0 {
                0
            } else {
                l_eval(a, env).max(y)
            }
        }
        Lvl::Param(n) => env.get(n).copied().unwrap_or(0),
    }
}

fn l_depth(l: &Lvl) -> u32 {
    match l {
        Lvl::Zero | Lvl::Param(_) => 0,
        Lvl::Succ(a) => 1 + l_depth(a),
        Lvl::Max(a, b) | Lvl::IMax(a, b) => l_depth(a).max(l_depth(b)),
    }
}

/// Equality as functions of the level parameters, checked on every assignment of
/// small values (enough to separate expressions built from `max`, `imax` and `+k`).
fn l_eq(a: &Lvl, b: &Lvl) -> bool {
    if a == b {
        return true;
    }
    let mut ps = Vec::new();
    l_params(a, &mut ps);
    l_params(b, &mut ps);
    let bound = l_depth(a).max(l_depth(b)) + 2;
    let mut vals = vec![0u32; ps.len()];
    loop {
        let env: HashMap<Name, u32> = ps.iter().cloned().zip(vals.iter().copied()).collect();
        if l_eval(a, &env) != l_eval(b, &env) {
            return false;
        }
        // next assignment
        let mut i = 0;
        loop {
            if i == vals.len() {
                return true;
            }
            vals[i] += 1;
            if vals[i] <= bound {
                break;
            }
            vals[i] = 0;
            i += 1;
        }
    }
}

fn l_is_zero(l: &Lvl) -> bool {
    l_eq(l, &Lvl::Zero)
}

// ---------------------------------------------------------------- declarations

#[derive(Clone)]
enum Decl {
    Axiom {
        lps: Vec<Name>,
        ty: Tm,
    },
    Def {
        lps: Vec<Name>,
        ty: Tm,
        val: Tm,
        height: u32,
    },
    Ind {
        lps: Vec<Name>,
        ty: Tm,
        nindices: usize,
        ctors: Vec<Name>,
        is_prop: bool,
        rec: Name,
    },
    Ctor {
        lps: Vec<Name>,
        ty: Tm,
        ind: Name,
        nparams: usize,
        nfields: usize,
    },
    Rec {
        lps: Vec<Name>,
        ty: Tm,
        nparams: usize,
        nindices: usize,
        nmotives: usize,
        nminors: usize,
        rules: Vec<(Name, usize, Tm)>,
    },
}

impl Decl {
    fn lps(&self) -> &[Name] {
        match self {
            Decl::Axiom { lps, .. }
            | Decl::Def { lps, .. }
            | Decl::Ind { lps, .. }
            | Decl::Ctor { lps, .. }
            | Decl::Rec { lps, .. } => lps,
        }
    }
    fn ty(&self) -> &Tm {
        match self {
            Decl::Axiom { ty, .. }
            | Decl::Def { ty, .. }
            | Decl::Ind { ty, .. }
            | Decl::Ctor { ty, .. }
            | Decl::Rec { ty, .. } => ty,
        }
    }
}

// ---------------------------------------------------------------- decoding

struct Blob<'a> {
    data: &'a [u8],
    pos: usize,
    names: Vec<Name>,
    nodes: Vec<Tm>,
}

impl<'a> Blob<'a> {
    fn byte(&mut self) -> Result<u8, String> {
        let b = *self.data.get(self.pos).ok_or("unexpected end of data")?;
        self.pos += 1;
        Ok(b)
    }
    fn var(&mut self) -> Result<u64, String> {
        Ok(self.var128()? as u64)
    }
    fn var128(&mut self) -> Result<u128, String> {
        let (mut n, mut shift) = (0u128, 0);
        loop {
            let b = self.byte()?;
            n |= ((b & 0x7f) as u128) << shift;
            if b & 0x80 == 0 {
                return Ok(n);
            }
            shift += 7;
            if shift > 127 {
                return Err("bad number".into());
            }
        }
    }
    fn name(&mut self) -> Result<Name, String> {
        let i = self.var()? as usize;
        self.names
            .get(i)
            .cloned()
            .ok_or_else(|| "bad name index".to_string())
    }
    fn level(&mut self) -> Result<Lvl, String> {
        Ok(match self.byte()? {
            0 => Lvl::Zero,
            1 => Lvl::Succ(Rc::new(self.level()?)),
            2 => {
                let a = self.level()?;
                Lvl::Max(Rc::new(a), Rc::new(self.level()?))
            }
            3 => {
                let a = self.level()?;
                Lvl::IMax(Rc::new(a), Rc::new(self.level()?))
            }
            4 => Lvl::Param(self.name()?),
            t => return Err(format!("bad level tag {t}")),
        })
    }
    fn node(&mut self) -> Result<Tm, String> {
        let get = |b: &Self, i: u64| b.nodes.get(i as usize).cloned().ok_or("bad node reference");
        Ok(Rc::new(match self.byte()? {
            0 => BVar(self.var()? as u32),
            1 => FVar(self.var()? as u32),
            3 => Sort(self.level()?),
            4 => {
                let n = self.name()?;
                let k = self.var()? as usize;
                let mut ls = Vec::new();
                for _ in 0..k {
                    ls.push(self.level()?);
                }
                Const(n, ls)
            }
            5 => Lit(self.var128()?),
            6 => Str(self.name()?),
            7 => {
                let (a, b) = (self.var()?, self.var()?);
                App(get(self, a)?, get(self, b)?)
            }
            8 | 9 => {
                let tag = self.data[self.pos - 1];
                let _mult = self.byte()?;
                let (a, b) = (self.var()?, self.var()?);
                if tag == 8 {
                    Lam(get(self, a)?, get(self, b)?)
                } else {
                    Pi(get(self, a)?, get(self, b)?)
                }
            }
            10 => {
                let _mult = self.byte()?;
                let (a, v, b) = (self.var()?, self.var()?, self.var()?);
                Let(get(self, a)?, get(self, v)?, get(self, b)?)
            }
            t => return Err(format!("bad term tag {t}")),
        }))
    }
}

/// Decode an export into declarations in dependency order.
fn decode(data: &[u8]) -> Result<Vec<(Name, Decl)>, String> {
    if !data.starts_with(b"APXV1") {
        return Err("not an APEX export (bad magic)".into());
    }
    let mut hdr = Blob {
        data,
        pos: 5,
        names: vec![],
        nodes: vec![],
    };
    let meta_len = hdr.var()? as usize;
    let meta_start = hdr.pos;
    let blob_start = meta_start + meta_len;
    // the term blob: names, then nodes
    let mut blob = Blob {
        data,
        pos: blob_start,
        names: vec![],
        nodes: vec![],
    };
    let nn = blob.var()? as usize;
    for _ in 0..nn {
        let len = blob.var()? as usize;
        let bytes = data.get(blob.pos..blob.pos + len).ok_or("truncated name")?;
        blob.names.push(
            std::str::from_utf8(bytes)
                .map_err(|_| "name is not UTF-8")?
                .into(),
        );
        blob.pos += len;
    }
    let count = blob.var()? as usize;
    for _ in 0..count {
        let n = blob.node()?;
        blob.nodes.push(n);
    }
    // the declaration table
    blob.pos = meta_start;
    let nd = blob.var()? as usize;
    let mut out = Vec::with_capacity(nd);
    for _ in 0..nd {
        let tag = blob.byte()?;
        let name = blob.name()?;
        let nl = blob.var()? as usize;
        let mut lps = Vec::new();
        for _ in 0..nl {
            lps.push(blob.name()?);
        }
        let ty_idx = blob.var()? as usize;
        let ty = blob.nodes.get(ty_idx).cloned().ok_or("bad type index")?;
        let node = |b: &Blob, i: u64| b.nodes.get(i as usize).cloned().ok_or("bad term index");
        let d = match tag {
            0 => Decl::Axiom { lps, ty },
            1 => {
                let v = blob.var()?;
                let val = node(&blob, v)?;
                let height = blob.var()? as u32;
                Decl::Def {
                    lps,
                    ty,
                    val,
                    height,
                }
            }
            2 => {
                let _nparams = blob.var()?;
                let nindices = blob.var()? as usize;
                let nc = blob.var()? as usize;
                let mut ctors = Vec::new();
                for _ in 0..nc {
                    ctors.push(blob.name()?);
                }
                let is_prop = blob.byte()? != 0;
                let rec = blob.name()?;
                let nf = blob.var()? as usize;
                for _ in 0..nf {
                    blob.name()?;
                }
                Decl::Ind {
                    lps,
                    ty,
                    nindices,
                    ctors,
                    is_prop,
                    rec,
                }
            }
            3 => {
                let ind = blob.name()?;
                let _idx = blob.var()?;
                let nparams = blob.var()? as usize;
                let nfields = blob.var()? as usize;
                Decl::Ctor {
                    lps,
                    ty,
                    ind,
                    nparams,
                    nfields,
                }
            }
            4 => {
                let _ind = blob.name()?;
                let nparams = blob.var()? as usize;
                let nindices = blob.var()? as usize;
                let nmotives = blob.var()? as usize;
                let nminors = blob.var()? as usize;
                let nr = blob.var()? as usize;
                let mut rules = Vec::new();
                for _ in 0..nr {
                    let c = blob.name()?;
                    let nf = blob.var()? as usize;
                    let r = blob.var()?;
                    rules.push((c, nf, node(&blob, r)?));
                }
                Decl::Rec {
                    lps,
                    ty,
                    nparams,
                    nindices,
                    nmotives,
                    nminors,
                    rules,
                }
            }
            t => return Err(format!("bad declaration tag {t}")),
        };
        out.push((name, d));
    }
    Ok(out)
}

// ---------------------------------------------------------------- checker

#[derive(Clone, Copy)]
pub struct Options {
    /// Compute `nat_sub`, `nat_div`, .. on literals directly (as the kernel does) instead of
    /// unfolding their definitions; `Nat.add`/`Nat.mul` on literals are always computed.
    pub accel: bool,
}

struct Checker<'a> {
    decls: &'a HashMap<Name, Decl>,
    /// types of free variables
    lctx: Vec<Tm>,
    opts: Options,
}

type Res<X> = Result<X, String>;

fn c(n: &str) -> Tm {
    Rc::new(Const(n.into(), vec![]))
}

impl<'a> Checker<'a> {
    fn fresh(&mut self, ty: Tm) -> u32 {
        self.lctx.push(ty);
        (self.lctx.len() - 1) as u32
    }

    fn pp(&self, t: &Tm) -> String {
        match &**t {
            BVar(i) => format!("#{i}"),
            FVar(i) => format!("_f{i}"),
            Sort(_) => "Sort".into(),
            Const(n, _) => n.to_string(),
            Lit(n) => n.to_string(),
            Str(s) => format!("{s:?}"),
            App(f, a) => format!("({} {})", self.pp(f), self.pp(a)),
            Lam(d, b) => format!("(fun {} => {})", self.pp(d), self.pp(b)),
            Pi(d, b) => format!("(({}) -> {})", self.pp(d), self.pp(b)),
            Let(_, v, b) => format!("(let {} in {})", self.pp(v), self.pp(b)),
        }
    }

    fn const_ty(&self, n: &Name, ls: &[Lvl]) -> Res<Tm> {
        let d = self
            .decls
            .get(n)
            .ok_or_else(|| format!("unknown constant `{n}`"))?;
        if d.lps().len() != ls.len() {
            return Err(format!(
                "`{n}` expects {} universe arguments, got {}",
                d.lps().len(),
                ls.len()
            ));
        }
        Ok(inst_lvls(d.ty(), d.lps(), ls))
    }

    // ----- reduction -----

    fn unfold(&self, t: &Tm) -> Option<Tm> {
        let (f, args) = spine(t);
        if let Const(n, ls) = &*f {
            if let Some(Decl::Def { lps, val, .. }) = self.decls.get(n) {
                if lps.len() == ls.len() {
                    return Some(apps(&inst_lvls(val, lps, ls), &args));
                }
            }
        }
        None
    }

    fn height(&self, t: &Tm) -> Option<(Name, u32)> {
        let (f, _) = spine(t);
        if let Const(n, ls) = &*f {
            if let Some(Decl::Def { lps, height, .. }) = self.decls.get(n) {
                if lps.len() == ls.len() {
                    return Some((n.clone(), *height));
                }
            }
        }
        None
    }

    fn nat_op(&mut self, f: &Tm, args: &[Tm]) -> Res<Option<Tm>> {
        let Const(n, _) = &**f else { return Ok(None) };
        let lib = !matches!(&**n, "Nat.add" | "Nat.mul");
        if args.len() != 2
            || !matches!(
                &**n,
                "Nat.add" | "Nat.mul" | "nat_sub" | "nat_beq" | "nat_lt" | "nat_div" | "nat_rem"
            )
            || (lib && (!self.opts.accel || !matches!(self.decls.get(n), Some(Decl::Def { .. }))))
        {
            return Ok(None);
        }
        let a = self.whnf(&args[0])?;
        let b = self.whnf(&args[1])?;
        let (Lit(x), Lit(y)) = (&*a, &*b) else {
            return Ok(None);
        };
        let (x, y) = (*x, *y);
        let lit = |v: u128| Rc::new(Lit(v));
        let boolean = |v: bool| c(if v { "Bool.true" } else { "Bool.false" });
        Ok(Some(match &**n {
            "Nat.add" => match x.checked_add(y) {
                Some(r) => lit(r),
                None => return Ok(None),
            },
            "Nat.mul" => match x.checked_mul(y) {
                Some(r) => lit(r),
                None => return Ok(None),
            },
            "nat_sub" => lit(x.saturating_sub(y)),
            "nat_beq" => boolean(x == y),
            "nat_lt" => boolean(x < y),
            "nat_div" => lit(x.checked_div(y).unwrap_or(0)),
            "nat_rem" => lit(if y == 0 { x } else { x % y }),
            _ => return Ok(None),
        }))
    }

    fn lit_ctor(n: u128) -> Tm {
        if n == 0 {
            c("Nat.zero")
        } else {
            app(c("Nat.succ"), Rc::new(Lit(n - 1)))
        }
    }

    fn iota(&mut self, f: &Tm, args: &[Tm]) -> Res<Option<Tm>> {
        let Const(n, ls) = &**f else { return Ok(None) };
        let Some(Decl::Rec {
            lps,
            nparams,
            nindices,
            nmotives,
            nminors,
            rules,
            ..
        }) = self.decls.get(n)
        else {
            return Ok(None);
        };
        let (lps, np, nm, nmi, ni) = (lps.clone(), *nparams, *nmotives, *nminors, *nindices);
        let rules = rules.clone();
        let major_idx = np + nm + nmi + ni;
        if args.len() <= major_idx || lps.len() != ls.len() {
            return Ok(None);
        }
        let mut major = self.whnf(&args[major_idx])?;
        if let Lit(k) = &*major {
            major = Self::lit_ctor(*k);
        }
        let (mh, margs) = spine(&major);
        let Const(cn, _) = &*mh else { return Ok(None) };
        let Some((_, nfields, rhs)) = rules.iter().find(|(r, _, _)| r == cn) else {
            return Ok(None);
        };
        let Some(Decl::Ctor { nparams: cp, .. }) = self.decls.get(cn) else {
            return Ok(None);
        };
        if margs.len() != cp + nfields {
            return Ok(None);
        }
        let rhs = inst_lvls(rhs, &lps, ls);
        let mut res = apps(&rhs, &args[..np + nm + nmi]);
        res = apps(&res, &margs[*cp..]);
        res = apps(&res, &args[major_idx + 1..]);
        Ok(Some(res))
    }

    fn quot(&mut self, f: &Tm, args: &[Tm]) -> Res<Option<Tm>> {
        let Const(n, _) = &**f else { return Ok(None) };
        if &**n != "Quot.lift" || args.len() < 6 {
            return Ok(None);
        }
        let q = self.whnf(&args[5])?;
        let (h, margs) = spine(&q);
        match &*h {
            Const(m, _) if &**m == "Quot.mk" && margs.len() == 3 => Ok(Some(apps(
                &args[3],
                &[vec![margs[2].clone()], args[6..].to_vec()].concat(),
            ))),
            _ => Ok(None),
        }
    }

    fn whnf_core(&mut self, t: &Tm) -> Res<Tm> {
        let mut cur = t.clone();
        loop {
            match &*cur.clone() {
                Let(_, v, b) => cur = inst(b, v),
                App(..) => {
                    let (f, args) = spine(&cur);
                    let f2 = self.whnf_core(&f)?;
                    match &*f2 {
                        Lam(..) => {
                            // β: one binder at a time
                            let mut body = f2.clone();
                            let mut i = 0;
                            while i < args.len() {
                                let next = match &*body {
                                    Lam(_, b) => inst(b, &args[i]),
                                    _ => break,
                                };
                                body = next;
                                i += 1;
                            }
                            cur = apps(&body, &args[i..]);
                        }
                        Const(..) => {
                            let r = match self.nat_op(&f2, &args)? {
                                Some(r) => Some(r),
                                None => match self.iota(&f2, &args)? {
                                    Some(r) => Some(r),
                                    None => self.quot(&f2, &args)?,
                                },
                            };
                            match r {
                                Some(r) => cur = r,
                                None => return Ok(if f == f2 { cur } else { apps(&f2, &args) }),
                            }
                        }
                        _ => return Ok(if f == f2 { cur } else { apps(&f2, &args) }),
                    }
                }
                _ => return Ok(cur),
            }
        }
    }

    fn whnf(&mut self, t: &Tm) -> Res<Tm> {
        let mut cur = t.clone();
        loop {
            cur = self.whnf_core(&cur)?;
            match self.unfold(&cur) {
                Some(n) => cur = n,
                None => return Ok(cur),
            }
        }
    }

    // ----- typing -----

    fn infer(&mut self, t: &Tm) -> Res<Tm> {
        match &**t {
            BVar(_) => Err("loose bound variable".into()),
            FVar(i) => self
                .lctx
                .get(*i as usize)
                .cloned()
                .ok_or_else(|| "unknown free variable".into()),
            Sort(l) => Ok(Rc::new(Sort(Lvl::Succ(Rc::new(l.clone()))))),
            Lit(_) => Ok(c("Nat")),
            Str(_) => Ok(c("String")),
            Const(n, ls) => self.const_ty(n, ls),
            App(f, a) => {
                let tf = self.infer(f)?;
                let tf = self.whnf(&tf)?;
                match &*tf {
                    Pi(d, b) => {
                        let ta = self.infer(a)?;
                        if !self.def_eq(&ta, d)? {
                            return Err(format!(
                                "application type mismatch: argument {} has type {}, expected {}",
                                self.pp(a),
                                self.pp(&ta),
                                self.pp(d)
                            ));
                        }
                        Ok(inst(b, a))
                    }
                    _ => Err(format!("function expected, got {}", self.pp(f))),
                }
            }
            Lam(d, b) => {
                self.sort_of(d)?;
                let x = self.fresh(d.clone());
                let tb = self.infer(&inst(b, &Rc::new(FVar(x))))?;
                Ok(Rc::new(Pi(d.clone(), abstract_fv(&tb, x, 0))))
            }
            Pi(d, b) => {
                let l1 = self.sort_of(d)?;
                let x = self.fresh(d.clone());
                let l2 = self.sort_of(&inst(b, &Rc::new(FVar(x))))?;
                Ok(Rc::new(Sort(Lvl::IMax(Rc::new(l1), Rc::new(l2)))))
            }
            Let(ty, v, b) => {
                self.sort_of(ty)?;
                let tv = self.infer(v)?;
                if !self.def_eq(&tv, ty)? {
                    return Err("let value has the wrong type".into());
                }
                self.infer(&inst(b, v))
            }
        }
    }

    /// `t` is a type: the level of its sort.
    fn sort_of(&mut self, t: &Tm) -> Res<Lvl> {
        let ty = self.infer(t)?;
        let w = self.whnf(&ty)?;
        match &*w {
            Sort(l) => Ok(l.clone()),
            _ => Err(format!("type expected, got {}", self.pp(t))),
        }
    }

    // ----- definitional equality -----

    fn def_eq(&mut self, a: &Tm, b: &Tm) -> Res<bool> {
        if a == b {
            return Ok(true);
        }
        let a = self.whnf_core(a)?;
        let b = self.whnf_core(b)?;
        if a == b {
            return Ok(true);
        }
        if let Some(r) = self.struct_eta(&a, &b)? {
            return Ok(r);
        }
        if let Some(r) = self.struct_eta(&b, &a)? {
            return Ok(r);
        }
        match (&*a, &*b) {
            (Lit(x), Lit(y)) => return Ok(x == y),
            (Lit(n), _) => {
                if let Some(r) = self.lit_vs(*n, &b)? {
                    return Ok(r);
                }
            }
            (_, Lit(n)) => {
                if let Some(r) = self.lit_vs(*n, &a)? {
                    return Ok(r);
                }
            }
            _ => {}
        }
        match (&*a, &*b) {
            (Sort(l1), Sort(l2)) => return Ok(l_eq(l1, l2)),
            (Pi(d1, b1), Pi(d2, b2)) | (Lam(d1, b1), Lam(d2, b2)) => {
                if !self.def_eq(d1, d2)? {
                    return Ok(false);
                }
                let x = Rc::new(FVar(self.fresh(d1.clone())));
                return self.def_eq(&inst(b1, &x), &inst(b2, &x));
            }
            (Lam(d, body), _) => {
                let x = Rc::new(FVar(self.fresh(d.clone())));
                return self.def_eq(&inst(body, &x), &app(b.clone(), x));
            }
            (_, Lam(d, body)) => {
                let x = Rc::new(FVar(self.fresh(d.clone())));
                return self.def_eq(&app(a.clone(), x.clone()), &inst(body, &x));
            }
            _ => {}
        }
        match (self.height(&a), self.height(&b)) {
            (None, None) => {}
            (Some(_), None) => {
                let ua = self.unfold(&a).expect("unfoldable");
                return self.def_eq(&ua, &b);
            }
            (None, Some(_)) => {
                let ub = self.unfold(&b).expect("unfoldable");
                return self.def_eq(&a, &ub);
            }
            (Some((na, ha)), Some((nb, hb))) => {
                if na == nb && self.spine_eq(&a, &b)? {
                    return Ok(true);
                }
                let ua = self.unfold(&a).expect("unfoldable");
                let ub = self.unfold(&b).expect("unfoldable");
                return match ha.cmp(&hb) {
                    std::cmp::Ordering::Greater => self.def_eq(&ua, &b),
                    std::cmp::Ordering::Less => self.def_eq(&a, &ub),
                    std::cmp::Ordering::Equal => self.def_eq(&ua, &ub),
                };
            }
        }
        if self.spine_eq(&a, &b)? {
            return Ok(true);
        }
        self.proof_irrelevant(&a, &b)
    }

    fn lit_vs(&mut self, n: u128, other: &Tm) -> Res<Option<bool>> {
        let (h, args) = spine(other);
        match (&*h, args.len()) {
            (Const(k, _), 0) if &**k == "Nat.zero" => Ok(Some(n == 0)),
            (Const(k, _), 1) if &**k == "Nat.succ" => {
                if n == 0 {
                    Ok(Some(false))
                } else {
                    Ok(Some(self.def_eq(&Rc::new(Lit(n - 1)), &args[0])?))
                }
            }
            _ => Ok(None),
        }
    }

    fn spine_eq(&mut self, a: &Tm, b: &Tm) -> Res<bool> {
        let (fa, aa) = spine(a);
        let (fb, ab) = spine(b);
        if aa.len() != ab.len() {
            return Ok(false);
        }
        let same = match (&*fa, &*fb) {
            (Const(n1, l1), Const(n2, l2)) => {
                n1 == n2 && l1.len() == l2.len() && l1.iter().zip(l2).all(|(x, y)| l_eq(x, y))
            }
            (FVar(i), FVar(j)) => i == j,
            _ => false,
        };
        if !same {
            return Ok(false);
        }
        for (x, y) in aa.iter().zip(&ab) {
            if !self.def_eq(x, y)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn proof_irrelevant(&mut self, a: &Tm, b: &Tm) -> Res<bool> {
        let Ok(ta) = self.infer(a) else {
            return Ok(false);
        };
        let is_prop = match self.sort_of(&ta) {
            Ok(l) => l_is_zero(&l),
            Err(_) => false,
        };
        if !is_prop {
            return Ok(false);
        }
        match self.infer(b) {
            Ok(tb) => self.def_eq(&ta, &tb),
            Err(_) => Ok(false),
        }
    }

    /// Structure η, exactly as the kernel states it (single constructor, no indices, not a
    /// proposition, field types independent of earlier fields).
    fn struct_eta(&mut self, ctor_side: &Tm, other: &Tm) -> Res<Option<bool>> {
        let (h, cargs) = spine(ctor_side);
        let Const(cname, clevels) = &*h else {
            return Ok(None);
        };
        let Some(Decl::Ctor {
            ind,
            nparams,
            nfields,
            ..
        }) = self.decls.get(cname).cloned()
        else {
            return Ok(None);
        };
        let Some(Decl::Ind {
            ctors,
            nindices,
            is_prop,
            rec,
            lps: ilps,
            ..
        }) = self.decls.get(&ind).cloned()
        else {
            return Ok(None);
        };
        if ctors.len() != 1 || nindices != 0 || is_prop {
            return Ok(None);
        }
        let Some(Decl::Rec {
            nmotives,
            lps: rlps,
            ..
        }) = self.decls.get(&rec).cloned()
        else {
            return Ok(None);
        };
        if nmotives != 1 || rlps.len() != ilps.len() + 1 {
            return Ok(None);
        }
        if cargs.len() != nparams + nfields {
            return Ok(None);
        }
        let (oh, _) = spine(other);
        if matches!(&*oh, Const(n, _) if n == cname) {
            return Ok(None);
        }
        let Ok(oty) = self.infer(other) else {
            return Ok(None);
        };
        let oty = self.whnf(&oty)?;
        let (th, targs) = spine(&oty);
        if !matches!(&*th, Const(n, _) if *n == ind) || targs.len() != nparams {
            return Ok(None);
        }
        // the constructor's field types, instantiated with the parameters
        let cty = self.const_ty(cname, clevels)?;
        let mut cur = cty;
        for p in &targs {
            let w = self.whnf(&cur)?;
            match &*w {
                Pi(_, b) => cur = inst(b, p),
                _ => return Ok(None),
            }
        }
        let mut fvs = Vec::new();
        let mut ftys = Vec::new();
        loop {
            let w = self.whnf(&cur)?;
            match &*w {
                Pi(d, b) => {
                    let x = self.fresh(d.clone());
                    ftys.push(d.clone());
                    fvs.push(x);
                    cur = inst(b, &Rc::new(FVar(x)));
                }
                _ => break,
            }
        }
        for (i, fty) in ftys.iter().enumerate() {
            if fvs[..i].iter().any(|&g| has_fvar(fty, g)) {
                return Ok(None);
            }
        }
        let this = apps(&Rc::new(Const(ind.clone(), clevels.clone())), &targs);
        for i in 0..fvs.len() {
            let lvl = self.sort_of(&ftys[i])?;
            let mut rec_levels = vec![lvl];
            rec_levels.extend(clevels.iter().cloned());
            let motive = Rc::new(Lam(this.clone(), ftys[i].clone()));
            // minor: fun fields => field_i
            let mut minor = Rc::new(FVar(fvs[i]));
            for (j, &g) in fvs.iter().enumerate().rev() {
                minor = Rc::new(Lam(abstract_fv(&ftys[j], g, 0), abstract_fv(&minor, g, 0)));
            }
            // the field types may mention earlier fields only if they depend on them; they
            // do not (checked above), so abstracting each binder type alone is exact
            let proj = apps(
                &Rc::new(Const(rec.clone(), rec_levels)),
                &[targs.clone(), vec![motive, minor, other.clone()]].concat(),
            );
            if !self.def_eq(&cargs[nparams + i], &proj)? {
                return Ok(Some(false));
            }
        }
        Ok(Some(true))
    }
}

// ---------------------------------------------------------------- driver

/// What `verify` reports.
#[derive(Debug, Default)]
pub struct Report {
    pub axioms: usize,
    pub definitions: usize,
    pub inductive_parts: usize,
}

/// Check an export produced by `Env::export`. Returns an error naming the first declaration
/// that does not check.
pub fn verify(data: &[u8], opts: Options) -> Result<Report, String> {
    let decls = decode(data)?;
    let mut table: HashMap<Name, Decl> = HashMap::new();
    let mut report = Report::default();
    // inductive types, constructors and recursors are given: they may refer to each other
    // (a recursor's rules mention the recursors of its whole mutual family)
    for (name, d) in &decls {
        if matches!(d, Decl::Ind { .. } | Decl::Ctor { .. } | Decl::Rec { .. }) {
            table.insert(name.clone(), d.clone());
        }
    }
    for (name, d) in decls {
        // checked against everything declared before it
        {
            let mut ck = Checker {
                decls: &table,
                lctx: Vec::new(),
                opts,
            };
            let ctx = |e: String| format!("`{name}`: {e}");
            match &d {
                Decl::Axiom { ty, .. } => {
                    ck.sort_of(ty).map_err(ctx)?;
                    report.axioms += 1;
                }
                Decl::Def { ty, val, .. } => {
                    ck.sort_of(ty).map_err(ctx)?;
                    let tv = ck.infer(val).map_err(ctx)?;
                    if !ck.def_eq(&tv, ty).map_err(ctx)? {
                        return Err(format!(
                            "`{name}`: the value has type {} but the declared type is {}",
                            ck.pp(&tv),
                            ck.pp(ty)
                        ));
                    }
                    report.definitions += 1;
                }
                // inductive types, constructors and recursors are given; their types must be sound
                Decl::Ind { ty, .. } | Decl::Ctor { ty, .. } => {
                    ck.sort_of(ty).map_err(ctx)?;
                    report.inductive_parts += 1;
                }
                Decl::Rec { ty, rules, .. } => {
                    ck.sort_of(ty).map_err(ctx)?;
                    for (_, _, rhs) in rules {
                        ck.infer(rhs).map_err(ctx)?;
                    }
                    report.inductive_parts += 1;
                }
            }
        }
        table.entry(name).or_insert(d);
    }
    Ok(report)
}
