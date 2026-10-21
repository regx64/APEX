//! A compact binary format for terms, so proofs and declarations can be stored and
//! re-checked: the proof cache of the library loader and the independent verifier read it.
//!
//! Terms are written as a DAG: every distinct node (by pointer) is emitted once, after
//! its children, and refers to them by index; strings and universe levels are interned.
//! Sharing therefore survives a round trip, which matters because tactic proofs share
//! their sub-terms heavily.

use crate::level::Level;
use crate::term::{Mult, Name, Term, T};
use std::collections::HashMap;
use std::rc::Rc;

pub struct Writer {
    out: Vec<u8>,
    nodes: u32,
    seen: HashMap<*const Term, u32>,
    names: Vec<Name>,
    name_idx: HashMap<Name, u32>,
    keep: Vec<T>,
}

fn varint(out: &mut Vec<u8>, mut n: u64) {
    loop {
        let b = (n & 0x7f) as u8;
        n >>= 7;
        if n == 0 {
            out.push(b);
            return;
        }
        out.push(b | 0x80);
    }
}

impl Default for Writer {
    fn default() -> Self {
        Self::new()
    }
}

impl Writer {
    pub fn new() -> Self {
        Writer {
            out: Vec::new(),
            nodes: 0,
            seen: HashMap::new(),
            names: Vec::new(),
            name_idx: HashMap::new(),
            keep: Vec::new(),
        }
    }

    /// The index of `n` in the blob's name table (added if new).
    pub fn intern(&mut self, n: &Name) -> u32 {
        self.name(n)
    }

    fn name(&mut self, n: &Name) -> u32 {
        if let Some(&i) = self.name_idx.get(n) {
            return i;
        }
        let i = self.names.len() as u32;
        self.names.push(n.clone());
        self.name_idx.insert(n.clone(), i);
        i
    }

    fn level(&mut self, l: &Level, buf: &mut Vec<u8>) {
        match l {
            Level::Zero => buf.push(0),
            Level::Succ(a) => {
                buf.push(1);
                self.level(a, buf);
            }
            Level::Max(a, b) => {
                buf.push(2);
                self.level(a, buf);
                self.level(b, buf);
            }
            Level::IMax(a, b) => {
                buf.push(3);
                self.level(a, buf);
                self.level(b, buf);
            }
            Level::Param(n) => {
                buf.push(4);
                let i = self.name(n);
                varint(buf, i as u64);
            }
            Level::MVar(_) => panic!("cannot serialize a term with a universe metavariable"),
        }
    }

    fn mult(m: Mult) -> u8 {
        match m {
            Mult::Zero => 0,
            Mult::One => 1,
            Mult::Omega => 2,
        }
    }

    /// Write `t` (and everything it refers to); the result is its node index.
    pub fn term(&mut self, t: &T) -> u32 {
        // iterative post-order to survive deep terms
        enum Frame {
            Enter(T),
            Exit(T),
        }
        let mut stack = vec![Frame::Enter(t.clone())];
        while let Some(f) = stack.pop() {
            match f {
                Frame::Enter(t) => {
                    let p = Rc::as_ptr(&t);
                    if self.seen.contains_key(&p) {
                        continue;
                    }
                    stack.push(Frame::Exit(t.clone()));
                    match &*t {
                        Term::App(a, b) => {
                            stack.push(Frame::Enter(b.clone()));
                            stack.push(Frame::Enter(a.clone()));
                        }
                        Term::Lam(_, a, b) | Term::Pi(_, a, b) => {
                            stack.push(Frame::Enter(b.clone()));
                            stack.push(Frame::Enter(a.clone()));
                        }
                        Term::Let(_, a, v, b) => {
                            stack.push(Frame::Enter(b.clone()));
                            stack.push(Frame::Enter(v.clone()));
                            stack.push(Frame::Enter(a.clone()));
                        }
                        _ => {}
                    }
                }
                Frame::Exit(t) => {
                    let p = Rc::as_ptr(&t);
                    if self.seen.contains_key(&p) {
                        continue;
                    }
                    let mut buf = Vec::new();
                    let idx = |w: &Self, c: &T| w.seen[&Rc::as_ptr(c)];
                    match &*t {
                        Term::BVar(i) => {
                            buf.push(0);
                            varint(&mut buf, *i as u64);
                        }
                        Term::FVar(i) => {
                            buf.push(1);
                            varint(&mut buf, *i as u64);
                        }
                        Term::MVar(_) => panic!("cannot serialize a term with a metavariable"),
                        Term::Sort(l) => {
                            buf.push(3);
                            self.level(l, &mut buf);
                        }
                        Term::Const(n, ls) => {
                            buf.push(4);
                            let i = self.name(n);
                            varint(&mut buf, i as u64);
                            varint(&mut buf, ls.len() as u64);
                            for l in ls {
                                self.level(l, &mut buf);
                            }
                        }
                        Term::Lit(n) => {
                            buf.push(5);
                            varint(&mut buf, *n);
                        }
                        Term::Str(s) => {
                            buf.push(6);
                            let i = self.name(s);
                            varint(&mut buf, i as u64);
                        }
                        Term::App(a, b) => {
                            buf.push(7);
                            varint(&mut buf, idx(self, a) as u64);
                            varint(&mut buf, idx(self, b) as u64);
                        }
                        Term::Lam(m, a, b) => {
                            buf.push(8);
                            buf.push(Self::mult(*m));
                            varint(&mut buf, idx(self, a) as u64);
                            varint(&mut buf, idx(self, b) as u64);
                        }
                        Term::Pi(m, a, b) => {
                            buf.push(9);
                            buf.push(Self::mult(*m));
                            varint(&mut buf, idx(self, a) as u64);
                            varint(&mut buf, idx(self, b) as u64);
                        }
                        Term::Let(m, a, v, b) => {
                            buf.push(10);
                            buf.push(Self::mult(*m));
                            varint(&mut buf, idx(self, a) as u64);
                            varint(&mut buf, idx(self, v) as u64);
                            varint(&mut buf, idx(self, b) as u64);
                        }
                    }
                    self.out.extend_from_slice(&buf);
                    self.seen.insert(p, self.nodes);
                    self.nodes += 1;
                    // keep the node alive so its address is not reused
                    self.keep.push(t.clone());
                }
            }
        }
        self.seen[&Rc::as_ptr(t)]
    }

    /// The finished blob: names, then nodes. Roots are recorded by the caller.
    pub fn finish(self) -> Vec<u8> {
        let mut head = Vec::new();
        varint(&mut head, self.names.len() as u64);
        for n in &self.names {
            varint(&mut head, n.len() as u64);
            head.extend_from_slice(n.as_bytes());
        }
        varint(&mut head, self.nodes as u64);
        head.extend_from_slice(&self.out);
        head
    }
}

pub struct Reader<'a> {
    data: &'a [u8],
    pos: usize,
    names: Vec<Name>,
    /// The terms in node order.
    pub terms: Vec<T>,
}

#[derive(Debug)]
pub struct DecodeError(pub String);

impl<'a> Reader<'a> {
    fn byte(&mut self) -> Result<u8, DecodeError> {
        let b = *self
            .data
            .get(self.pos)
            .ok_or_else(|| DecodeError("unexpected end of data".into()))?;
        self.pos += 1;
        Ok(b)
    }

    fn varint(&mut self) -> Result<u64, DecodeError> {
        let mut n = 0u64;
        let mut shift = 0;
        loop {
            let b = self.byte()?;
            n |= ((b & 0x7f) as u64) << shift;
            if b & 0x80 == 0 {
                return Ok(n);
            }
            shift += 7;
            if shift > 63 {
                return Err(DecodeError("bad number".into()));
            }
        }
    }

    fn name(&mut self) -> Result<Name, DecodeError> {
        let i = self.varint()? as usize;
        self.names
            .get(i)
            .cloned()
            .ok_or_else(|| DecodeError("bad name index".into()))
    }

    fn level(&mut self) -> Result<Level, DecodeError> {
        Ok(match self.byte()? {
            0 => Level::Zero,
            1 => Level::Succ(Rc::new(self.level()?)),
            2 => {
                let a = self.level()?;
                Level::Max(Rc::new(a), Rc::new(self.level()?))
            }
            3 => {
                let a = self.level()?;
                Level::IMax(Rc::new(a), Rc::new(self.level()?))
            }
            4 => Level::Param(self.name()?),
            t => return Err(DecodeError(format!("bad level tag {t}"))),
        })
    }

    fn mult(&mut self) -> Result<Mult, DecodeError> {
        Ok(match self.byte()? {
            0 => Mult::Zero,
            1 => Mult::One,
            2 => Mult::Omega,
            t => return Err(DecodeError(format!("bad multiplicity {t}"))),
        })
    }

    fn node(&mut self) -> Result<T, DecodeError> {
        let get = |r: &Self, i: u64| -> Result<T, DecodeError> {
            r.terms
                .get(i as usize)
                .cloned()
                .ok_or_else(|| DecodeError("forward node reference".into()))
        };
        Ok(match self.byte()? {
            0 => Rc::new(Term::BVar(self.varint()? as u32)),
            1 => Rc::new(Term::FVar(self.varint()? as u32)),
            3 => Rc::new(Term::Sort(self.level()?)),
            4 => {
                let n = self.name()?;
                let k = self.varint()? as usize;
                let mut ls = Vec::with_capacity(k);
                for _ in 0..k {
                    ls.push(self.level()?);
                }
                Rc::new(Term::Const(n, ls))
            }
            5 => Rc::new(Term::Lit(self.varint()?)),
            6 => Rc::new(Term::Str(self.name()?)),
            7 => {
                let (a, b) = (self.varint()?, self.varint()?);
                Rc::new(Term::App(get(self, a)?, get(self, b)?))
            }
            8 => {
                let m = self.mult()?;
                let (a, b) = (self.varint()?, self.varint()?);
                Rc::new(Term::Lam(m, get(self, a)?, get(self, b)?))
            }
            9 => {
                let m = self.mult()?;
                let (a, b) = (self.varint()?, self.varint()?);
                Rc::new(Term::Pi(m, get(self, a)?, get(self, b)?))
            }
            10 => {
                let m = self.mult()?;
                let (a, v, b) = (self.varint()?, self.varint()?, self.varint()?);
                Rc::new(Term::Let(m, get(self, a)?, get(self, v)?, get(self, b)?))
            }
            t => return Err(DecodeError(format!("bad term tag {t}"))),
        })
    }

    /// Decode a blob written by `Writer::finish`.
    pub fn new(data: &'a [u8]) -> Result<Reader<'a>, DecodeError> {
        let mut r = Reader {
            data,
            pos: 0,
            names: Vec::new(),
            terms: Vec::new(),
        };
        let nn = r.varint()? as usize;
        for _ in 0..nn {
            let len = r.varint()? as usize;
            let bytes = r
                .data
                .get(r.pos..r.pos + len)
                .ok_or_else(|| DecodeError("truncated name".into()))?;
            let s =
                std::str::from_utf8(bytes).map_err(|_| DecodeError("name is not UTF-8".into()))?;
            r.names.push(s.into());
            r.pos += len;
        }
        let count = r.varint()? as usize;
        for _ in 0..count {
            let t = r.node()?;
            r.terms.push(t);
        }
        Ok(r)
    }

    pub fn term(&self, idx: u32) -> Result<T, DecodeError> {
        self.terms
            .get(idx as usize)
            .cloned()
            .ok_or_else(|| DecodeError("bad term index".into()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::*;

    #[test]
    fn round_trip_keeps_terms_and_sharing() {
        let x = cnst("Nat".into(), vec![Level::param("u").succ()]);
        let f = lam(Mult::Omega, x.clone(), app(bvar(0), x.clone()));
        let t = app(f.clone(), f);
        let mut w = Writer::new();
        let i = w.term(&t);
        let blob = w.finish();
        let r = Reader::new(&blob).unwrap();
        let back = r.term(i).unwrap();
        assert_eq!(t, back);
        // the shared lambda is stored once
        assert!(r.terms.len() <= 6);
    }
}
