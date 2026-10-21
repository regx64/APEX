//! A native backend: `apex compile` writes a C program (the erased IR of everything `main`
//! reaches, as data, plus a C port of the lazy machine in `runtime.c`) that `cc` turns into a
//! standalone executable. It is a compiler in the sense that the result needs neither the
//! checker nor this crate; it is not an optimizing one: the machine is the same lazy
//! environment machine as the interpreter's.

use crate::erase::{Eraser, Ir};
use apex_kernel::{Decl, Env};
use std::collections::HashMap;
use std::fmt::Write;
use std::rc::Rc;

const RUNTIME: &str = include_str!("runtime.c");

const PRIMS: &[(&str, &str, usize)] = &[
    ("Nat.succ", "P_NAT_SUCC", 1),
    ("Nat.add", "P_NAT_ADD", 2),
    ("Nat.mul", "P_NAT_MUL", 2),
    ("String.append", "P_STR_APPEND", 2),
    ("String.length", "P_STR_LENGTH", 1),
    ("String.beq", "P_STR_BEQ", 2),
    ("nat_sub", "P_NAT_SUB", 2),
    ("nat_div", "P_NAT_DIV", 2),
    ("nat_rem", "P_NAT_REM", 2),
    ("nat_beq", "P_NAT_BEQ", 2),
    ("nat_lt", "P_NAT_LT", 2),
    ("WellFounded.fix", "P_WF_FIX", 6),
    ("WellFounded.fix.ih", "P_WF_IH", 7),
    ("Quot.mk", "P_QUOT_MK", 3),
    ("Quot.lift", "P_QUOT_LIFT", 6),
    ("Nat.toString", "P_NAT_TO_STRING", 1),
    ("IO.pure", "P_IO_PURE", 2),
    ("IO.bind", "P_IO_BIND", 4),
    ("IO.print", "P_IO_PRINT", 1),
];

#[derive(Default)]
struct GlobOut {
    kind: &'static str,
    name: String,
    arity: usize,
    nparams: usize,
    nmotives: usize,
    nminors: usize,
    nindices: usize,
    nrules: usize,
    rules_off: usize,
    ir: usize,
    prim: &'static str,
}

struct IrOut {
    kind: &'static str,
    a: usize,
    b: usize,
    lo: u64,
    hi: u64,
    s: String,
    len: usize,
}

struct RuleOut {
    ctor: String,
    nfields: usize,
    rhs: usize,
}

struct Compiler<'a> {
    env: &'a Env,
    gids: HashMap<String, usize>,
    globs: Vec<GlobOut>,
    queue: Vec<String>,
    ir: Vec<IrOut>,
    memo: HashMap<*const Ir, usize>,
    rules: Vec<RuleOut>,
}

fn c_string(s: &str) -> String {
    let mut out = String::from("\"");
    for b in s.bytes() {
        match b {
            b'"' => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            0x20..=0x7e if b != b'?' => out.push(b as char),
            _ => {
                let _ = write!(out, "\\{b:03o}");
            }
        }
    }
    out.push('"');
    out
}

impl<'a> Compiler<'a> {
    fn gid(&mut self, name: &str) -> usize {
        if let Some(&g) = self.gids.get(name) {
            return g;
        }
        let g = self.globs.len();
        self.globs.push(GlobOut::default());
        self.gids.insert(name.to_string(), g);
        self.queue.push(name.to_string());
        g
    }

    fn emit(&mut self, ir: &Rc<Ir>) -> usize {
        if let Some(&i) = self.memo.get(&Rc::as_ptr(ir)) {
            return i;
        }
        let mut n = IrOut {
            kind: "K_ERASED",
            a: 0,
            b: 0,
            lo: 0,
            hi: 0,
            s: String::new(),
            len: 0,
        };
        match &**ir {
            Ir::Var(i) => {
                n.kind = "K_VAR";
                n.lo = *i as u64;
            }
            Ir::Lam(b) => {
                n.kind = "K_LAM";
                n.a = self.emit(b);
            }
            Ir::App(f, a) => {
                n.kind = "K_APP";
                n.a = self.emit(f);
                n.b = self.emit(a);
            }
            Ir::Global(g) => {
                n.kind = "K_GLOBAL";
                n.a = self.gid(g);
            }
            Ir::Erased => {}
            Ir::Nat(v) => {
                n.kind = "K_NAT";
                n.lo = *v as u64;
                n.hi = (*v >> 64) as u64;
            }
            Ir::Str(s) => {
                n.kind = "K_STR";
                n.s = s.to_string();
                n.len = s.len();
            }
            Ir::Let(v, b) => {
                n.kind = "K_LET";
                n.a = self.emit(v);
                n.b = self.emit(b);
            }
        }
        let i = self.ir.len();
        self.ir.push(n);
        self.memo.insert(Rc::as_ptr(ir), i);
        i
    }

    fn define(&mut self, name: &str) -> Result<(), String> {
        let g = self.gids[name];
        let mut out = GlobOut {
            name: name.to_string(),
            kind: "G_ERASED",
            prim: "0",
            ..Default::default()
        };
        if name == "Nat.zero" {
            out.kind = "G_NATLIT";
        } else if let Some((_, p, ar)) = PRIMS.iter().find(|(n, _, _)| *n == name) {
            out.kind = "G_PRIM";
            out.prim = p;
            out.arity = *ar;
        } else {
            match self.env.get(name) {
                Some(Decl::Def { val, .. }) => {
                    let ir = Eraser::new(self.env).erase_closed(val)?;
                    out.kind = "G_DEF";
                    self.memo.clear();
                    out.ir = self.emit(&ir);
                }
                Some(Decl::Ctor(ci)) => {
                    out.kind = "G_CTOR";
                    out.arity = ci.nparams + ci.nfields;
                    out.nparams = ci.nparams;
                }
                Some(Decl::Rec(r)) => {
                    out.kind = "G_REC";
                    out.arity = r.nparams + r.nmotives + r.nminors + r.nindices + 1;
                    out.nparams = r.nparams;
                    out.nmotives = r.nmotives;
                    out.nminors = r.nminors;
                    out.nindices = r.nindices;
                    out.nrules = r.rules.len();
                    out.rules_off = self.rules.len();
                    for ru in &r.rules {
                        let ir = Eraser::new(self.env).erase_closed(&ru.rhs)?;
                        self.memo.clear();
                        let rhs = self.emit(&ir);
                        self.rules.push(RuleOut {
                            ctor: ru.ctor.to_string(),
                            nfields: ru.nfields,
                            rhs,
                        });
                        // constructors the recursor can meet must be known to the runtime
                        self.gid(&ru.ctor);
                    }
                }
                Some(Decl::Inductive(_)) => {}
                Some(Decl::Axiom { .. }) => {
                    return Err(format!("the axiom `{name}` has no runtime value"))
                }
                None => return Err(format!("unknown constant `{name}`")),
            }
        }
        self.globs[g] = out;
        Ok(())
    }
}

/// The C source of the program whose entry point is `main`.
pub fn emit_c(env: &Env) -> Result<String, String> {
    let Some(decl) = env.get("main") else {
        return Err("no `main` function: define `fn main() -> T { .. }`".into());
    };
    let (head, _) = apex_kernel::term::app_spine(decl.ty());
    let is_io = matches!(&*head, apex_kernel::Term::Const(n, _) if &**n == "IO");
    let mut c = Compiler {
        env,
        gids: HashMap::new(),
        globs: Vec::new(),
        queue: Vec::new(),
        ir: Vec::new(),
        memo: HashMap::new(),
        rules: Vec::new(),
    };
    let main = c.gid("main");
    for n in [
        "Bool.true",
        "Bool.false",
        "Unit.unit",
        "Nat.zero",
        "Nat.succ",
    ] {
        if env.get(n).is_some() || n == "Nat.zero" {
            c.gid(n);
        }
    }
    let wf_fix = c.gid("WellFounded.fix");
    let wf_ih = c.gid("WellFounded.fix.ih");
    while let Some(n) = c.queue.pop() {
        c.define(&n)?;
    }
    let mut out = String::new();
    out.push_str("/* generated by `apex compile` */\n");
    out.push_str("typedef struct { int kind; int a, b; unsigned long long lo, hi; const char *s; unsigned long len; } IrNode;\n");
    out.push_str("typedef struct { int kind; const char *name; int arity, nparams, nmotives, nminors, nindices, nrules, rules_off, ir, prim; } Glob;\n");
    out.push_str("typedef struct { const char *ctor; int nfields; int rhs; } Rule;\n");
    out.push_str("enum { K_VAR, K_LAM, K_APP, K_GLOBAL, K_ERASED, K_NAT, K_STR, K_LET };\n");
    out.push_str("enum { G_DEF, G_CTOR, G_REC, G_PRIM, G_ERASED, G_NATLIT };\n");
    out.push_str("enum {");
    for (i, (_, p, _)) in PRIMS.iter().enumerate() {
        let _ = write!(out, "{}{p}", if i == 0 { " " } else { ", " });
    }
    out.push_str(" };\n");
    let _ = writeln!(out, "#define NGLOBS {}", c.globs.len());
    let _ = writeln!(out, "#define NRULES {}", c.rules.len());
    let _ = writeln!(out, "#define MAIN_GID {main}");
    let _ = writeln!(out, "#define MAIN_IS_IO {}", is_io as u8);
    let _ = writeln!(out, "#define WF_FIX_GID {wf_fix}");
    let _ = writeln!(out, "#define WF_IH_GID {wf_ih}");
    out.push_str("static const IrNode IR[] = {\n");
    for n in &c.ir {
        let s = if n.s.is_empty() && n.kind != "K_STR" {
            "0".to_string()
        } else {
            c_string(&n.s)
        };
        let _ = writeln!(
            out,
            "  {{{}, {}, {}, {}ULL, {}ULL, {}, {}}},",
            n.kind, n.a, n.b, n.lo, n.hi, s, n.len
        );
    }
    out.push_str("  {K_ERASED, 0, 0, 0, 0, 0, 0}\n};\n");
    out.push_str("static const Rule RULES[] = {\n");
    for r in &c.rules {
        let _ = writeln!(
            out,
            "  {{{}, {}, {}}},",
            c_string(&r.ctor),
            r.nfields,
            r.rhs
        );
    }
    out.push_str("  {0, 0, 0}\n};\n");
    out.push_str("static const Glob GLOBS[] = {\n");
    for g in &c.globs {
        let _ = writeln!(
            out,
            "  {{{}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}}},",
            g.kind,
            c_string(&g.name),
            g.arity,
            g.nparams,
            g.nmotives,
            g.nminors,
            g.nindices,
            g.nrules,
            g.rules_off,
            g.ir,
            g.prim
        );
    }
    out.push_str("  {G_ERASED, \"\", 0, 0, 0, 0, 0, 0, 0, 0, 0}\n};\n");
    out.push_str(RUNTIME);
    Ok(out)
}
