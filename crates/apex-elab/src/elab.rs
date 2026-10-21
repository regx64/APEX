//! Bidirectional elaboration with metavariables and implicit arguments.

use apex_borrowck::{callee_of, Callee, ParamKind};
use apex_kernel::prelude::add_prelude;
use apex_kernel::term::*;
use apex_kernel::{Decl, Env, InductiveDecl, KResult, KernelError, Level, Mult, TypeChecker};
use apex_span::Span;
use apex_syntax::ast::*;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElabError {
    pub msg: String,
    pub span: Span,
    /// An error code such as `E0499`, for borrow errors.
    pub code: Option<String>,
    /// Secondary locations, shown as notes.
    pub notes: Vec<(Span, String)>,
}

impl ElabError {
    pub fn new(span: Span, msg: impl Into<String>) -> ElabError {
        ElabError {
            msg: msg.into(),
            span,
            code: None,
            notes: vec![],
        }
    }
}

mod derive;
mod mutual;
mod tactic;
mod wf;

type R<X> = Result<X, ElabError>;

fn err<X>(span: Span, msg: impl Into<String>) -> R<X> {
    Err(ElabError::new(span, msg))
}

fn from_kernel<X>(r: KResult<X>, span: Span) -> R<X> {
    r.map_err(|KernelError(msg)| ElabError::new(span, msg))
}

/// An argument to an application: surface syntax, or an already elaborated term.
enum Arg<'e> {
    Expr(&'e Expr),
    Term(T),
    /// A method receiver: the elaborated value, and the expression it came from
    /// (which is the place to borrow when the method takes `&mut self`).
    Recv(T, &'e Expr),
}

enum Res {
    Local(T),
    Global(String),
}

/// How an application supplies a binder: written out, inferred by unification,
/// or found by instance search.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Bk {
    Exp,
    Imp,
    Inst,
}

/// Scope entries of `let mut` variables (and `&mut` parameters) carry this prefix.
const MUT: char = '\u{1}';

fn mut_key(name: &str) -> String {
    format!("{MUT}{name}")
}

fn plain_name(n: &str) -> &str {
    n.strip_prefix(MUT).unwrap_or(n)
}

// ---- pairs: how mutation is threaded through branches and `&mut` calls ----

fn prod_ty(a: &T, b: &T) -> T {
    mk_apps(&cnst("Prod".into(), vec![]), &[a.clone(), b.clone()])
}

fn prod_mk(at: &T, bt: &T, a: T, b: T) -> T {
    mk_apps(
        &cnst("Prod.mk".into(), vec![]),
        &[at.clone(), bt.clone(), a, b],
    )
}

fn prod_fst(at: &T, bt: &T, p: T) -> T {
    mk_apps(
        &cnst("Prod.fst".into(), vec![]),
        &[at.clone(), bt.clone(), p],
    )
}

fn prod_snd(at: &T, bt: &T, p: T) -> T {
    mk_apps(
        &cnst("Prod.snd".into(), vec![]),
        &[at.clone(), bt.clone(), p],
    )
}

/// `A1 × (A2 × (.. × An))`, or `A1` when there is one.
fn tuple_ty(tys: &[T]) -> T {
    match tys {
        [one] => one.clone(),
        [first, rest @ ..] => prod_ty(first, &tuple_ty(rest)),
        [] => unreachable!("tuples have at least one component"),
    }
}

fn tuple_mk(tys: &[T], vals: &[T]) -> T {
    match (tys, vals) {
        ([_], [v]) => v.clone(),
        ([t, rest_t @ ..], [v, rest_v @ ..]) => {
            prod_mk(t, &tuple_ty(rest_t), v.clone(), tuple_mk(rest_t, rest_v))
        }
        _ => unreachable!("one value per type"),
    }
}

/// Component `i` of a tuple built by `tuple_mk`.
fn tuple_get(tys: &[T], p: T, i: usize) -> T {
    match tys {
        [_] => p,
        [first, rest @ ..] => {
            if i == 0 {
                prod_fst(first, &tuple_ty(rest), p)
            } else {
                tuple_get(rest, prod_snd(first, &tuple_ty(rest), p), i - 1)
            }
        }
        [] => unreachable!(),
    }
}

fn sig_error(e: apex_borrowck::SigError) -> ElabError {
    ElabError::new(e.span, e.msg)
}

fn borrow_error(d: apex_borrowck::Diag) -> ElabError {
    ElabError {
        msg: d.msg,
        span: d.span,
        code: (d.code != "APEX").then(|| d.code.to_string()),
        notes: d.notes,
    }
}

/// A variable, a field of a place, or a dereference of one.
fn is_place_expr(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Var(_) => true,
        ExprKind::Field(b, _) | ExprKind::Deref(b) => is_place_expr(b),
        _ => false,
    }
}

/// The component types of a tuple type built by `tuple_ty` with `k` components.
fn split_tuple_ty(s: &T, k: usize) -> Vec<T> {
    if k == 1 {
        return vec![s.clone()];
    }
    let (_, args) = app_spine(s);
    let mut v = vec![args[0].clone()];
    v.extend(split_tuple_ty(&args[1], k - 1));
    v
}

fn synth_var(name: &str, span: Span) -> Expr {
    Expr {
        kind: ExprKind::Var(name.into()),
        span,
    }
}

/// `(w1, (w2, ..))` as syntax: `Prod.mk(w1, Prod.mk(w2, ..))`.
fn state_tuple_expr(names: &[String], span: Span) -> Expr {
    match names {
        [one] => synth_var(one, span),
        [first, rest @ ..] => Expr {
            kind: ExprKind::Call(
                Box::new(synth_var("Prod.mk", span)),
                vec![synth_var(first, span), state_tuple_expr(rest, span)],
            ),
            span,
        },
        [] => unreachable!("at least one mutable variable"),
    }
}

/// Component `i` of `k` as syntax: `s`, `s.fst`, `s.snd.fst`, ..
fn state_proj_expr(base: Expr, i: usize, k: usize) -> Expr {
    let span = base.span;
    let field = |b: Expr, f: &str| Expr {
        kind: ExprKind::Field(
            Box::new(b),
            Ident {
                name: f.into(),
                span,
            },
        ),
        span,
    };
    if k == 1 {
        base
    } else if i == 0 {
        field(base, "fst")
    } else {
        state_proj_expr(field(base, "snd"), i - 1, k - 1)
    }
}

/// `{ stmts; tail }` with the tail turned into a statement and `pure(state)` as the new tail.
fn block_with_state_tail(b: &Block, names: &[String]) -> Block {
    let mut stmts = b.stmts.clone();
    if let Some(t) = &b.tail {
        stmts.push(Stmt::Expr((**t).clone()));
    }
    let pure = Expr {
        kind: ExprKind::Call(
            Box::new(synth_var("IO.pure", b.span)),
            vec![state_tuple_expr(names, b.span)],
        ),
        span: b.span,
    };
    Block {
        stmts,
        tail: Some(Box::new(pure)),
        span: b.span,
    }
}

/// Make every branch of a `do` statement end with `pure(state)`.
fn add_state_tail(e: &Expr, names: &[String]) -> Expr {
    let kind = match &e.kind {
        ExprKind::Block(b) => ExprKind::Block(block_with_state_tail(b, names)),
        ExprKind::If(c, then, els) => {
            let empty = Block {
                stmts: vec![],
                tail: None,
                span: e.span,
            };
            ExprKind::If(
                c.clone(),
                block_with_state_tail(then, names),
                Some(Box::new(match els {
                    Some(x) => add_state_tail(x, names),
                    None => Expr {
                        kind: ExprKind::Block(block_with_state_tail(&empty, names)),
                        span: e.span,
                    },
                })),
            )
        }
        ExprKind::Match(s, arms) => ExprKind::Match(
            s.clone(),
            arms.iter()
                .map(|a| Arm {
                    pat: a.pat.clone(),
                    body: match &a.body.kind {
                        ExprKind::Block(b) => Expr {
                            kind: ExprKind::Block(block_with_state_tail(b, names)),
                            span: a.body.span,
                        },
                        _ => {
                            let single = Block {
                                stmts: vec![],
                                tail: Some(Box::new(a.body.clone())),
                                span: a.body.span,
                            };
                            Expr {
                                kind: ExprKind::Block(block_with_state_tail(&single, names)),
                                span: a.body.span,
                            }
                        }
                    },
                })
                .collect(),
        ),
        other => other.clone(),
    };
    Expr { kind, span: e.span }
}

/// An assignable place: a mutable variable and a path of struct fields.
struct Place {
    name: String,
    idx: usize,
    path: Vec<String>,
}

/// The mutable variables threaded through a branching construct.
#[derive(Clone)]
struct StateCtx {
    /// The type of the construct's own value.
    r: T,
    vars: Vec<(String, usize)>,
    tys: Vec<T>,
}

#[derive(Clone)]
struct StructMeta {
    ctor: String,
    nparams: usize,
    fields: Vec<String>,
}

/// A trait bound: the trait's name and its explicit type arguments.
type Bound<'e> = (String, &'e [Expr]);

/// Which binders of a constant's type are implicit.
type Masks = HashMap<String, Vec<Bk>>;
type Aliases = HashMap<String, String>;

/// Trait bookkeeping shared by all declarations.
#[derive(Default)]
struct Tables {
    /// Declared universe level names (`universe u;`), in declaration order.
    universes: Vec<String>,
    /// trait name -> its methods (in field order)
    traits: HashMap<String, TraitInfo>,
    /// trait name -> instance definitions
    insts: HashMap<String, Vec<String>>,
    /// method name -> traits declaring it
    methods: HashMap<String, Vec<String>>,
    /// A user definition that shares a name with a prelude one is stored under a
    /// different kernel name; this maps the source name to it.
    shadow: HashMap<String, String>,
    /// struct name -> constructor and field names (for field assignment)
    structs: HashMap<String, StructMeta>,
    /// How each function takes its arguments (`&`, `&mut`, `own`), by kernel name.
    sigs: HashMap<String, Callee>,
    /// Theorems marked `#[simp]`, in declaration order (kernel names).
    simp: Vec<String>,
    /// The enclosing `namespace` path, outermost first.
    ns: Vec<String>,
    /// Namespaces brought into scope by `open`.
    opens: Vec<String>,
    /// `variable` declarations of the enclosing sections.
    vars: Vec<Param>,
    /// Struct declarations (after flattening `extends`), for children and `derive`.
    struct_decls: HashMap<String, StructDecl>,
    /// Operators and macros declared by the files elaborated so far.
    notations: Notations,
}

#[derive(Clone)]
struct TraitInfo {
    /// number of class parameters, `Self` included
    nparams: usize,
    methods: Vec<String>,
    /// names of the trait's own type parameters (after `Self`)
    generics: Vec<String>,
    /// which class parameters (`Self` first) are outputs, found by the implementation
    outs: Vec<bool>,
    /// methods that have a default body
    defaults: HashMap<String, FnDecl>,
}

/// An impl under construction: sibling methods already built can be used by
/// later methods, but the impl cannot be used as a whole until it is finished.
struct Pending {
    trait_name: String,
    class_args: Vec<T>,
    built: Vec<Option<T>>,
    /// placeholders for methods not built yet
    holes: Vec<u32>,
    methods: Vec<String>,
}

/// Marker in the error raised when a method needs one that is not built yet.
const NOT_BUILT: &str = "is used before it is defined";

pub struct Elaborator {
    env: Env,
    masks: Masks,
    aliases: Aliases,
    tables: Tables,
    inst_counter: usize,
    /// set once the prelude is loaded: later definitions may shadow prelude names
    prelude_loaded: bool,
    user_defs: std::collections::HashSet<String>,
    /// The proof cache of the library being loaded, if any.
    lib_cache: Option<crate::libcache::LibCache>,
}

impl Default for Elaborator {
    fn default() -> Self {
        Self::new()
    }
}

impl Elaborator {
    /// An elaborator with the kernel prelude and `prelude.apex` loaded.
    pub fn new() -> Elaborator {
        let mut env = Env::new();
        add_prelude(&mut env).expect("kernel prelude must check");
        let mut masks = Masks::new();
        masks.insert("Eq".into(), vec![Bk::Imp, Bk::Exp, Bk::Exp]);
        masks.insert("Eq.refl".into(), vec![Bk::Imp, Bk::Exp]);
        masks.insert("IO.pure".into(), vec![Bk::Imp, Bk::Exp]);
        use Bk::{Exp, Imp};
        for (n, m) in [
            ("Eq.subst", vec![Imp, Imp, Imp, Exp, Exp, Exp]),
            ("Eq.symm", vec![Imp, Imp, Imp, Exp]),
            ("Eq.trans", vec![Imp, Imp, Imp, Imp, Exp, Exp]),
            ("congr_arg", vec![Imp, Imp, Imp, Imp, Exp, Exp]),
            ("False.elim", vec![Imp, Exp]),
            ("Not", vec![Exp]),
            ("And", vec![Exp, Exp]),
            ("And.intro", vec![Imp, Imp, Exp, Exp]),
            ("And.left", vec![Imp, Imp, Exp]),
            ("And.right", vec![Imp, Imp, Exp]),
            ("Or", vec![Exp, Exp]),
            ("Or.inl", vec![Imp, Imp, Exp]),
            ("Or.inr", vec![Imp, Imp, Exp]),
            ("Quot", vec![Imp, Exp]),
            ("Quot.mk", vec![Imp, Exp, Exp]),
            ("Quot.lift", vec![Imp, Imp, Imp, Exp, Exp, Exp]),
            ("Quot.ind", vec![Imp, Imp, Imp, Exp, Exp]),
            ("Quot.sound", vec![Imp, Imp, Imp, Imp, Exp]),
            ("funext", vec![Imp, Imp, Imp, Imp, Exp]),
            ("propext", vec![Imp, Imp, Exp, Exp]),
            ("Classical.choice", vec![Imp, Exp]),
            ("Nonempty", vec![Exp]),
            ("Nonempty.intro", vec![Imp, Exp]),
            ("Acc", vec![Imp, Exp, Exp]),
            ("Acc.intro", vec![Imp, Imp, Exp, Exp]),
            ("Acc.fix", vec![Imp, Imp, Imp, Exp, Exp, Exp]),
            ("WellFounded", vec![Imp, Exp]),
            ("WellFounded.fix", vec![Imp, Imp, Imp, Exp, Exp, Exp]),
            ("WellFounded.fix_eq", vec![Imp, Imp, Imp, Exp, Exp, Exp]),
            ("Exists", vec![Imp, Exp]),
            ("Exists.intro", vec![Imp, Imp, Exp, Exp]),
        ] {
            masks.insert(n.into(), m);
        }
        masks.insert("List".into(), vec![Bk::Exp]);
        masks.insert("List.nil".into(), vec![Bk::Imp]);
        masks.insert("List.cons".into(), vec![Bk::Imp, Bk::Exp, Bk::Exp]);
        masks.insert("IO.bind".into(), vec![Bk::Imp, Bk::Imp, Bk::Exp, Bk::Exp]);
        let mut aliases = Aliases::new();
        aliases.insert("true".into(), "Bool.true".into());
        aliases.insert("false".into(), "Bool.false".into());
        aliases.insert("print".into(), "IO.print".into());
        aliases.insert("pure".into(), "IO.pure".into());
        let mut el = Elaborator {
            env,
            masks,
            aliases,
            tables: Tables::default(),
            inst_counter: 0,
            prelude_loaded: false,
            user_defs: Default::default(),
            lib_cache: None,
        };
        let src = include_str!("prelude.apex");
        let module = apex_syntax::parse(src).expect("prelude must parse");
        el.elab_module(&module).unwrap_or_else(|e| {
            let (line, _) = e.span.line_col(src);
            panic!(
                "prelude must elaborate: {} (prelude.apex line {line})",
                e.msg
            )
        });
        el.prelude_loaded = true;
        el
    }

    /// Elaborate a bundled library (names count as prelude names: a program may define its
    /// own and shadow them). Its theorem proofs come from the proof cache when it has them.
    fn load_lib(&mut self, id: &str, src: &'static str) {
        let module = apex_syntax::parse(src)
            .unwrap_or_else(|e| panic!("{id} prelude must parse: {}", e.msg));
        self.lib_cache = Some(crate::libcache::LibCache::open(id, src));
        self.prelude_loaded = false;
        let result = self.elab_module(&module);
        self.prelude_loaded = true;
        if let Some(c) = self.lib_cache.take() {
            if result.is_ok() {
                c.save();
            }
        }
        result.unwrap_or_else(|e| {
            let (line, _) = e.span.line_col(src);
            panic!(
                "{id} prelude must elaborate: {} (prelude_{id}.apex line {line})",
                e.msg
            )
        });
    }

    /// Load the verified arithmetic library behind `omega` (order on `Nat`, the
    /// reflected linear-expression language, and the certificate checker). It costs
    /// startup time, so it is loaded only for programs that use it.
    pub fn load_omega(&mut self) {
        if self.env.get("omega_sound").is_none() {
            self.load_lib("omega", include_str!("prelude_omega.apex"));
        }
    }

    /// Load the verified `ring` normalizer (and the arithmetic library it uses).
    pub fn load_ring(&mut self) {
        if self.env.get("ring_sound").is_none() {
            self.load_omega();
            self.load_lib("ring", include_str!("prelude_ring.apex"));
        }
    }

    /// Load the integers (`Int`) with their verified laws; they use `omega` and `ring`.
    pub fn load_int(&mut self) {
        if self.env.get("int_add_comm").is_none() {
            self.load_ring();
            self.load_lib("int", include_str!("prelude_int.apex"));
        }
    }

    /// Load the elementary number theory library.
    pub fn load_math(&mut self) {
        if self.env.get("gauss").is_none() {
            self.load_std();
            self.load_ring();
            self.load_lib("math", include_str!("prelude_math.apex"));
        }
    }

    /// Load `Array`, `Map` and the extra `Nat` functions (needs `Option`, lists and omega).
    pub fn load_std(&mut self) {
        if self.env.get("array_push").is_none() {
            self.load_data();
            self.load_omega();
            self.load_lib("std", include_str!("prelude_std.apex"));
        }
    }

    /// Load `Option`, `Subtype` and `Sigma`.
    pub fn load_data(&mut self) {
        if self.env.get("option_map").is_none() {
            self.load_lib("data", include_str!("prelude_data.apex"));
        }
    }

    /// Load classical logic (`em`, `by_contradiction`); `by_cases` and `by_contra` need it.
    pub fn load_classical(&mut self) {
        if self.env.get("em").is_none() {
            self.load_lib("classical", include_str!("prelude_classical.apex"));
        }
    }

    /// Load the libraries a program refers to. They are loaded on demand because they
    /// cost startup time: `omega` and well-founded recursion need the arithmetic
    /// library; naming one of the list lemmas loads the core library (which needs it too).
    pub fn load_libs_for(&mut self, src: &str) {
        let mentions = |w: &str| {
            src.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '.'))
                .any(|x| x == w)
        };
        // a name the program declares itself is not a reason to load the library
        let declares = |w: &str| {
            ["fn", "theorem", "struct", "enum"].iter().any(|kw| {
                src.match_indices(&format!("{kw} {w}")).any(|(i, m)| {
                    !src[i + m.len()..].starts_with(|c: char| c.is_alphanumeric() || c == '_')
                })
            })
        };
        let mentions = |w: &str| mentions(w) && !declares(w);
        let core = include_str!("prelude_core.apex");
        let core_names: Vec<String> = apex_syntax::parse(core)
            .map(|m| {
                m.items
                    .iter()
                    .filter_map(|i| match &i.kind {
                        ItemKind::Theorem(t) => Some(t.name.name.clone()),
                        _ => None,
                    })
                    .collect()
            })
            .unwrap_or_default();
        if mentions("ring") {
            self.load_ring();
        }
        if [
            "dvd", "is_even", "is_odd", "gauss", "sum_to", "sum_sq", "fib", "is_prime", "pow_add",
        ]
        .iter()
        .any(|n| mentions(n))
        {
            self.load_math();
        }
        if ["Array", "Map", "nat_pow", "nat_min", "nat_max", "nat_gcd"]
            .iter()
            .any(|n| mentions(n))
        {
            self.load_std();
        }
        if ["Option", "Subtype", "Sigma"].iter().any(|n| mentions(n)) {
            self.load_data();
        }
        if mentions("Int") || mentions("int_add_comm") {
            self.load_int();
        }
        if mentions("em")
            || mentions("by_contradiction")
            || mentions("not_not")
            || src.contains("by_cases")
            || src.contains("by_contra")
        {
            self.load_classical();
        }
        if core_names.iter().any(|n| mentions(n)) {
            self.load_omega();
            self.load_core();
        } else if ["omega", "linarith", "termination_by", "decreasing_by"]
            .iter()
            .any(|w| src.contains(w))
            || mentions("le")
            || mentions("lt")
            || ["<=", ">=", "!=", "<->"].iter().any(|op| src.contains(op))
        {
            self.load_omega();
        }
    }

    fn load_core(&mut self) {
        if self.env.get("list_append_nil").is_none() {
            self.load_lib("core", include_str!("prelude_core.apex"));
        }
    }

    pub fn env(&self) -> &Env {
        &self.env
    }

    pub fn elab_module(&mut self, m: &Module) -> R<()> {
        let n = &m.notations;
        self.tables.notations.infix.extend(n.infix.clone());
        self.tables.notations.prefix.extend(n.prefix.clone());
        self.tables.notations.macros.extend(n.macros.clone());
        self.tables.notations.tactics.extend(n.tactics.clone());
        let timing = std::env::var_os("APEX_TIME").is_some();
        for item in &m.items {
            let t0 = std::time::Instant::now();
            self.elab_item(item)?;
            if timing {
                let ms = t0.elapsed().as_millis();
                if ms >= 20 {
                    eprintln!("[time] {ms} ms: item at byte {}", item.span.start);
                }
            }
        }
        Ok(())
    }

    fn elab_item(&mut self, item: &Item) -> R<()> {
        match &item.kind {
            ItemKind::Fn(f) => self.elab_fn(f, item.span),
            ItemKind::Theorem(t) => self.elab_theorem(t, item.span),
            ItemKind::Enum(e) => self.elab_enum_item(e, item.span),
            ItemKind::Struct(s) => self.elab_struct_item(s, item.span),
            ItemKind::Trait(t) => self.elab_trait(t, item.span),
            ItemKind::Impl(i) => self.elab_impl(i, item.span),
            ItemKind::Namespace { name, items } => {
                let saved = (
                    self.tables.ns.len(),
                    self.tables.opens.len(),
                    self.tables.vars.len(),
                );
                self.tables
                    .ns
                    .extend(name.split('.').map(|s| s.to_string()));
                let r = items.iter().try_for_each(|i| self.elab_item(i));
                self.tables.ns.truncate(saved.0);
                self.tables.opens.truncate(saved.1);
                self.tables.vars.truncate(saved.2);
                r
            }
            ItemKind::Section(items) => {
                let saved = (self.tables.opens.len(), self.tables.vars.len());
                let r = items.iter().try_for_each(|i| self.elab_item(i));
                self.tables.opens.truncate(saved.0);
                self.tables.vars.truncate(saved.1);
                r
            }
            ItemKind::Import(_) | ItemKind::Notation(_) => Ok(()), // loaded by the driver / applied by the parser
            ItemKind::Mutual(items) => self.elab_mutual(items, item.span),
            ItemKind::Universe(names) => {
                for n in names {
                    if !self.tables.universes.contains(&n.name) {
                        self.tables.universes.push(n.name.clone());
                    }
                }
                Ok(())
            }
            ItemKind::Open(name) => {
                self.tables.opens.push(name.clone());
                Ok(())
            }
            ItemKind::Variable(params) => {
                self.tables.vars.extend(params.iter().cloned());
                Ok(())
            }
        }
    }

    /// `mutual { enum A .. enum B .. }`: mutually inductive types.
    fn elab_mutual(&mut self, items: &[Item], span: Span) -> R<()> {
        let mut enums = Vec::new();
        let mut fns = Vec::new();
        for it in items {
            match &it.kind {
                ItemKind::Enum(e) => enums.push(e),
                ItemKind::Fn(f) => fns.push(f),
                _ => {
                    return err(
                        it.span,
                        "only `enum` or only `fn` declarations can be in a `mutual` block",
                    )
                }
            }
        }
        if !fns.is_empty() {
            if !enums.is_empty() {
                return err(
                    span,
                    "a `mutual` block is either all enums or all functions",
                );
            }
            return self.elab_mutual_fns(&fns, span);
        }
        if enums.is_empty() {
            return err(span, "an empty `mutual` block");
        }
        self.elab_enum_family(&enums, span)
    }

    /// The kernel-visible name of a declaration made in the current namespace.
    fn qualified(&self, name: &Ident) -> Ident {
        if self.tables.ns.is_empty() {
            return name.clone();
        }
        Ident {
            name: format!("{}.{}", self.tables.ns.join("."), name.name),
            span: name.span,
        }
    }

    /// The `variable`s of the enclosing sections that a declaration mentions.
    fn used_vars(&self, mentions: &dyn Fn(&str) -> bool) -> Vec<Param> {
        self.tables
            .vars
            .iter()
            .filter(|v| mentions(&v.name.name))
            .cloned()
            .collect()
    }

    fn cx(&self) -> Cx<'_> {
        Cx::new(&self.env, &self.masks, &self.aliases, &self.tables)
    }

    fn add_def(&mut self, name: &Ident, ty: T, val: T, mask: Vec<Bk>) -> R<()> {
        self.add_def_named(name, ty, val, mask).map(|_| ())
    }

    /// Add a definition and return the kernel name it was stored under.
    fn add_def_named(&mut self, name: &Ident, ty: T, val: T, mask: Vec<Bk>) -> R<String> {
        self.add_def_named_opts(name, ty, val, mask, false)
    }

    /// `trusted`: the value comes from the proof cache and is not checked again.
    fn add_def_named_opts(
        &mut self,
        name: &Ident,
        ty: T,
        val: T,
        mask: Vec<Bk>,
        trusted: bool,
    ) -> R<String> {
        // a user definition may shadow a prelude one; it then lives under another kernel name
        let mut kname = name.name.clone();
        if self.prelude_loaded {
            if self.user_defs.contains(&name.name) {
                return err(name.span, format!("`{}` is already declared", name.name));
            }
            if self.env.get(&name.name).is_some() {
                kname = format!("{}'user", name.name);
                self.tables.shadow.insert(name.name.clone(), kname.clone());
            }
            self.user_defs.insert(name.name.clone());
        }
        // universe parameters: the declared level names this definition mentions
        let mut used: Vec<Name> = Vec::new();
        collect_level_params(&ty, &mut used);
        collect_level_params(&val, &mut used);
        let mut lps: Vec<String> = self
            .tables
            .universes
            .iter()
            .filter(|u| used.iter().any(|x| &**x == u.as_str()))
            .cloned()
            .collect();
        for u in &used {
            if !lps.iter().any(|x| x.as_str() == &**u) {
                lps.push(u.to_string());
            }
        }
        let lps: Vec<&str> = lps.iter().map(String::as_str).collect();
        if trusted {
            from_kernel(self.env.add_def_trusted(&kname, &lps, ty, val), name.span)?;
        } else {
            from_kernel(self.env.add_def(&kname, &lps, ty, val), name.span)?;
        }
        self.masks.insert(kname.clone(), mask);
        Ok(kname)
    }

    fn elab_fn(&mut self, f: &FnDecl, span: Span) -> R<()> {
        let used = self.used_vars(&|v| {
            f.params.iter().any(|p| mentions_expr(&p.ty, v))
                || f.ret.as_ref().is_some_and(|r| mentions_expr(r, v))
                || f.body.as_ref().is_some_and(|b| mentions_block(b, v))
        });
        if used.is_empty() {
            return self.elab_fn_inner(f, span);
        }
        let mut g = f.clone();
        g.params = used.into_iter().chain(g.params).collect();
        self.elab_fn_inner(&g, span)
    }

    fn elab_fn_inner(&mut self, f: &FnDecl, span: Span) -> R<()> {
        let callee = callee_of(f, &[]).map_err(sig_error)?;
        let recursive = f
            .body
            .as_ref()
            .is_some_and(|b| mentions_block(b, &f.name.name));
        if recursive && callee.has_mut_params() {
            return err(
                f.name.span,
                "a recursive function cannot have `&mut` parameters yet",
            );
        }
        if recursive && f.wf.is_some() {
            return self.elab_wf_fn(f, span);
        }
        let (ty, val, mask) = if !recursive {
            self.try_fn(f, span, None, false, None)?
        } else {
            // structural recursion: try each parameter as the decreasing one
            let mut first_err = None;
            let mut found = None;
            // first plain structural recursion (direct fields), then course-of-values
            // recursion through `brecOn`, which sees all deeper subterms
            'search: for deep in [false, true] {
                for k in 0..f.params.len() {
                    match self.try_fn(f, span, Some(k), deep, None) {
                        Ok(r) => {
                            found = Some(r);
                            break 'search;
                        }
                        Err(e) => {
                            if std::env::var_os("APEX_DEBUG").is_some() {
                                eprintln!("[structural attempt deep={deep} k={k}] {}", e.msg);
                            }
                            // the course-of-values attempt is the more capable one
                            if deep && k == 0 || first_err.is_none() {
                                first_err = Some(e);
                            }
                        }
                    }
                }
            }
            match found {
                Some(r) => r,
                // not structural: try a parameter as a `Nat` measure with `omega`
                None if f.params.iter().any(|p| !p.name.name.is_empty()) => {
                    return self.elab_wf_fn(f, span).map_err(|wf_err| {
                        // report the structural failure, and why well-founded recursion failed
                        match first_err.clone() {
                            Some(mut e) => {
                                let why = wf_err.msg.lines().next().unwrap_or("").to_string();
                                e.msg = format!(
                                    "{}\nhelp: nor is it provably terminating on a parameter ({why}); \
                                     add `termination_by <measure>` (and `decreasing_by {{ .. }}`)",
                                    e.msg
                                );
                                e
                            }
                            None => wf_err,
                        }
                    });
                }
                None => {
                    return Err(first_err.unwrap_or(ElabError::new(
                        f.name.span,
                        "a recursive function needs at least one parameter to recurse on",
                    )))
                }
            }
        };
        let qname = self.qualified(&f.name);
        let kname = self.add_def_named(&qname, ty, val, mask)?;
        self.tables.sigs.insert(kname, callee);
        Ok(())
    }

    /// Elaborate a function; `decr` is the index (among `params`) of the
    /// parameter a recursive function decreases on.
    fn try_fn(
        &self,
        f: &FnDecl,
        span: Span,
        decr: Option<usize>,
        deep: bool,
        self_ty: Option<&Expr>,
    ) -> R<(T, T, Vec<Bk>)> {
        let mut cx = self.cx();
        let (mut fvs, mut mask) = cx.elab_binders(&f.generics, &[])?;
        if let Some(e) = self_ty {
            let t = cx.elab_type(e)?;
            cx.scope.push(("Self".into(), t));
        }
        let (pf, pm) = cx.elab_binders(&[], &f.params)?;
        fvs.extend(pf);
        mask.extend(pm);
        if let Some(k) = decr {
            let nparams = f.params.len();
            let explicit: Vec<u32> = fvs[fvs.len() - nparams..].to_vec();
            let d = explicit[k];
            let dty = from_kernel(cx.tc.local_ty(d), span)?;
            let dty = from_kernel(cx.tc.whnf(&dty), span)?;
            let (h, _) = app_spine(&dty);
            let inductive = matches!(&*h, Term::Const(n, _) if matches!(self.env.get(n), Some(Decl::Inductive(_))));
            if !inductive {
                return err(
                    f.params[k].name.span,
                    "cannot recurse on a parameter whose type is not an inductive type",
                );
            }
            cx.rec = Some(RecCtx {
                name: f.name.name.clone(),
                decr: d,
                explicit,
                fields: HashMap::new(),
                refined: Vec::new(),
                in_top: false,
                deep: None,
                wf: None,
                mutual: None,
            });
        }
        let ret = match &f.ret {
            Some(t) => cx.elab_type(t)?,
            None => cx.unit_type(),
        };
        if deep && cx.rec.is_some() {
            let d = cx.setup_deep(&ret, f.name.span)?;
            if let Some(rc) = cx.rec.as_mut() {
                rc.deep = Some(d);
            }
        }
        let Some(block) = &f.body else {
            return err(f.name.span, "a function needs a body");
        };
        let mvars = cx.mut_params(&f.params);
        let ret_full = cx.with_mut_result(&ret, &mvars)?;
        let body = cx.scoped(|cx| {
            let v = cx.elab_block_opts(block, Some(&ret), true)?;
            let v = cx.coerce(v, &ret, block.span)?;
            cx.wrap_mut_result(&ret, &mvars, v)
        })?;
        let body = match cx
            .rec
            .as_ref()
            .and_then(|rc| rc.deep.clone().map(|d| (d, rc)))
        {
            Some((d, rc)) => {
                let (decr, explicit) = (rc.decr, rc.explicit.clone());
                cx.wrap_brec(&d, decr, &explicit, body)?
            }
            None => body,
        };
        cx.borrow_check(f)?;
        Ok((
            cx.close(&fvs, &ret_full, true, span)?,
            cx.close(&fvs, &body, false, span)?,
            mask,
        ))
    }

    fn elab_theorem(&mut self, t: &TheoremDecl, span: Span) -> R<()> {
        let used = self.used_vars(&|v| {
            t.params.iter().any(|p| mentions_expr(&p.ty, v))
                || mentions_expr(&t.stmt, v)
                || match &t.proof {
                    Proof::Term(e) => mentions_expr(e, v),
                    Proof::Tactic(toks) => toks
                        .iter()
                        .any(|tk| matches!(&tk.kind, apex_syntax::TokenKind::Ident(n) if n == v)),
                }
        });
        if used.is_empty() {
            return self.elab_theorem_inner(t, span);
        }
        let mut t2 = t.clone();
        t2.params = used.into_iter().chain(t2.params).collect();
        self.elab_theorem_inner(&t2, span)
    }

    fn elab_theorem_inner(&mut self, t: &TheoremDecl, span: Span) -> R<()> {
        let qname = self.qualified(&t.name);
        // a bundled library's proof, checked when the cache was written
        let cached = self.lib_cache.as_ref().and_then(|c| c.get(&qname.name));
        let (ty, val, mask) = {
            let mut cx = self.cx();
            let (fvs, mask) = cx.elab_binders(&t.generics, &t.params)?;
            let stmt = cx.elab_type(&t.stmt)?;
            let val = match &cached {
                Some(v) => v.clone(),
                None => {
                    let proof = match &t.proof {
                        Proof::Term(e) => cx.elab_check(e, &stmt)?,
                        Proof::Tactic(toks) => {
                            let tacs =
                                apex_syntax::parse_tactics(toks, span, &self.tables.notations)
                                    .map_err(|e| ElabError::new(e.span, e.msg))?;
                            cx.prove(&stmt, &tacs, span)?
                        }
                    };
                    cx.close(&fvs, &proof, false, span)?
                }
            };
            (cx.close(&fvs, &stmt, true, span)?, val, mask)
        };
        let kernel_name =
            self.add_def_named_opts(&qname, ty, val.clone(), mask, cached.is_some())?;
        if cached.is_none() {
            if let Some(c) = self.lib_cache.as_mut() {
                c.record(&kernel_name, &val);
            }
        }
        if t.simp {
            self.tables.simp.push(kernel_name);
        }
        Ok(())
    }

    /// The type of an inductive type former: `Π params, Sort level`.
    fn ind_type(&self, generics: &[Generic], level: u32, span: Span) -> R<T> {
        let mut cx = self.cx();
        let (pfv, _) = cx.elab_binders(generics, &[])?;
        let declared = generics
            .iter()
            .filter(|g| !g.name.name.starts_with('\''))
            .count();
        if pfv.len() != declared {
            return err(
                span,
                "trait bounds on type declarations are not supported yet",
            );
        }
        cx.close(&pfv, &sort(Level::of_nat(level)), true, span)
    }

    fn register_inductive(&mut self, decl: InductiveDecl, nparams: usize, span: Span) -> R<()> {
        let name = decl.name.to_string();
        let ctor_names: Vec<String> = decl.ctors.iter().map(|(n, _)| n.to_string()).collect();
        from_kernel(self.env.add_inductive(decl), span)?;
        for cn in ctor_names {
            // parameters are implicit in constructors
            self.masks.insert(cn.clone(), vec![Bk::Imp; nparams]);
            if let Some(short) = cn.strip_prefix(&format!("{name}.")) {
                if short != "mk"
                    && self.env.get(short).is_none()
                    && !self.aliases.contains_key(short)
                {
                    self.aliases.insert(short.to_string(), cn.clone());
                }
            }
        }
        Ok(())
    }

    fn elab_enum(&mut self, d: &EnumDecl, span: Span) -> R<()> {
        self.elab_enum_family(&[d], span)
    }

    /// One or several (`mutual { enum A .. enum B .. }`) enums, as one inductive family.
    fn elab_enum_family(&mut self, ds: &[&EnumDecl], span: Span) -> R<()> {
        if ds.iter().any(|d| !d.indices.is_empty()) {
            // dependent `match` and index equations use the arithmetic library
            self.load_omega();
        }
        let nparams = ds[0]
            .generics
            .iter()
            .filter(|g| !g.name.name.starts_with('\''))
            .count();
        let mut level0 = None;
        let mut ind_tys = Vec::new();
        for d in ds {
            // `: Prop` makes an inductive predicate, otherwise a `Type`
            let level = match d.sort.as_ref().map(|e| &e.kind) {
                None => 1,
                Some(ExprKind::Var(n)) if n == "Type" => 1,
                Some(ExprKind::Var(n)) if n == "Prop" => 0,
                Some(_) => {
                    return err(
                        d.sort.as_ref().map_or(span, |e| e.span),
                        "an enum is a `Type` or a `Prop`",
                    )
                }
            };
            if *level0.get_or_insert(level) != level {
                return err(
                    d.name.span,
                    "the enums of a `mutual` group must all be `Type` or all `Prop`",
                );
            }
            let declared = d
                .generics
                .iter()
                .filter(|g| !g.name.name.starts_with('\''))
                .count();
            if declared != nparams {
                return err(
                    d.name.span,
                    "the enums of a `mutual` group must have the same type parameters",
                );
            }
            let mut cx = self.cx();
            let (pfv, _) = cx.elab_binders(&d.generics, &[])?;
            if pfv.len() != declared {
                return err(
                    span,
                    "trait bounds on type declarations are not supported yet",
                );
            }
            let mut all = pfv;
            for (n, t) in &d.indices {
                let ty = cx.elab_type(t)?;
                let fv = cx.tc.fresh(&n.name, ty, Mult::Omega);
                cx.scope.push((n.name.clone(), fvar(fv)));
                all.push(fv);
            }
            ind_tys.push(cx.close(&all, &sort(Level::of_nat(level)), true, span)?);
        }
        // scratch environment in which all the types are visible, for recursive fields
        let mut scratch = self.env.clone();
        for (d, ty) in ds.iter().zip(&ind_tys) {
            from_kernel(
                scratch.add_axiom(&d.name.name, &[], ty.clone()),
                d.name.span,
            )?;
        }
        let mut types = Vec::new();
        let mut local_counts: Vec<(String, usize)> = Vec::new();
        for (d, ind_ty) in ds.iter().zip(&ind_tys) {
            let name = d.name.name.clone();
            let mut ctors: Vec<(Name, T)> = Vec::new();
            let mut cx = Cx::new(&scratch, &self.masks, &self.aliases, &self.tables);
            for v in &d.variants {
                let (pfv, _) = cx.elab_binders(&d.generics, &[])?;
                // constructor-local implicit binders (the indices' variables)
                let (lfv, _) = cx.elab_binders(&v.generics, &[])?;
                let mut fields = Vec::new();
                for ft in &v.fields {
                    let ty = cx.elab_type(ft)?;
                    fields.push(cx.tc.fresh("_", ty, Mult::Omega));
                }
                let pargs: Vec<T> = pfv.iter().map(|&i| fvar(i)).collect();
                let result = match &v.result {
                    Some(e) => cx.elab_type(e)?,
                    None => {
                        if !d.indices.is_empty() {
                            return err(
                                v.name.span,
                                format!(
                                    "constructor `{}` of an indexed family needs a result type: `: {}(..)`",
                                    v.name.name, name
                                ),
                            );
                        }
                        mk_apps(&cnst(name.as_str().into(), vec![]), &pargs)
                    }
                };
                cx.solve_goals(true)?;
                let all: Vec<u32> = pfv.iter().chain(&lfv).chain(&fields).copied().collect();
                let cty = cx.close(&all, &result, true, v.name.span)?;
                let cname = format!("{name}.{}", v.name.name);
                local_counts.push((cname.clone(), lfv.len()));
                ctors.push((cname.as_str().into(), cty));
                cx.scope.clear();
            }
            types.push(apex_kernel::TypeDecl {
                name: name.as_str().into(),
                ty: ind_ty.clone(),
                ctors,
            });
        }
        let cnames: Vec<String> = types
            .iter()
            .flat_map(|t| t.ctors.iter().map(|(n, _)| n.to_string()))
            .collect();
        from_kernel(
            self.env.add_mutual(apex_kernel::MutualDecl {
                lparams: vec![],
                nparams,
                types,
            }),
            span,
        )?;
        for d in ds {
            let name = &d.name.name;
            for v in &d.variants {
                let cn = format!("{name}.{}", v.name.name);
                // parameters are implicit in constructors
                self.masks.insert(cn.clone(), vec![Bk::Imp; nparams]);
                if v.name.name != "mk"
                    && self.env.get(&v.name.name).is_none()
                    && !self.aliases.contains_key(&v.name.name)
                {
                    self.aliases.insert(v.name.name.clone(), cn);
                }
            }
        }
        // constructor-local binders are implicit too
        for (cn, n) in local_counts {
            debug_assert!(cnames.contains(&cn));
            self.masks.insert(cn, vec![Bk::Imp; nparams + n]);
        }
        Ok(())
    }

    fn elab_struct(&mut self, d: &StructDecl, span: Span) -> R<()> {
        let ind_ty = self.ind_type(&d.generics, 1, span)?;
        let name = d.name.name.clone();
        let nparams = d
            .generics
            .iter()
            .filter(|g| !g.name.name.starts_with('\''))
            .count();
        let ctor_name = format!("{name}.mk");
        let mut scratch = self.env.clone();
        from_kernel(scratch.add_axiom(&name, &[], ind_ty.clone()), d.name.span)?;
        let ctor_ty = {
            let mut cx = Cx::new(&scratch, &self.masks, &self.aliases, &self.tables);
            let tele = cx.struct_telescope(d)?;
            let result = mk_apps(&cnst(name.as_str().into(), vec![]), &tele.pargs());
            let all: Vec<u32> = tele.params.iter().chain(&tele.fields).copied().collect();
            cx.close(&all, &result, true, span)?
        };
        self.register_inductive(
            InductiveDecl {
                name: name.as_str().into(),
                lparams: vec![],
                nparams,
                ty: ind_ty,
                ctors: vec![(ctor_name.as_str().into(), ctor_ty)],
            },
            nparams,
            span,
        )?;
        self.tables.structs.insert(
            name.clone(),
            StructMeta {
                ctor: format!("{name}.mk"),
                nparams,
                fields: d.fields.iter().map(|f| f.name.name.clone()).collect(),
            },
        );
        // projections: S.f := fun params (self : S params) => S.rec (fun _ => T_f) (fun fields => f) self
        for (j, field) in d.fields.iter().enumerate() {
            self.add_projection(&name, nparams, j, &field.name, Bk::Exp, &|cx| {
                cx.struct_telescope(d)
            })?;
        }
        Ok(())
    }

    /// `N.f := fun params (s : N params) => N.rec (fun _ => T_f) (fun fields => f) s`.
    /// `last` says how the final binder (the structure or the instance) is supplied.
    fn add_projection(
        &mut self,
        ind: &str,
        nparams: usize,
        j: usize,
        fname: &Ident,
        last: Bk,
        mk_tele: &dyn Fn(&mut Cx<'_>) -> R<StructTele>,
    ) -> R<()> {
        let (ty, val, extra) = {
            let mut cx = self.cx();
            let tele = mk_tele(&mut cx)?;
            let fty0 = tele.field_tys[j].clone();
            let self_ty = mk_apps(&cnst(ind.into(), vec![]), &tele.pargs());
            let s = cx.tc.fresh("self", self_ty.clone(), Mult::Omega);
            let t0 = cx.tc.fresh("t", self_ty, Mult::Omega);
            // a field type may mention earlier fields: through their projections
            let with_proj = |cx: &Cx<'_>, who: u32| -> T {
                let _ = cx;
                let mut t = fty0.clone();
                for (k, &fk) in tele.fields[..j].iter().enumerate() {
                    if contains_fvar(&t, fk) {
                        let pk = mk_apps(
                            &cnst(
                                format!("{ind}.{}", tele.field_names[k]).as_str().into(),
                                vec![],
                            ),
                            &[tele.pargs(), vec![fvar(who)]].concat(),
                        );
                        t = instantiate(&abstract_fvars(&t, &[fk]), &pk);
                    }
                }
                t
            };
            let fty = with_proj(&cx, s);
            let fty_motive = with_proj(&cx, t0);
            let lvl = from_kernel(cx.tc.check_is_type(&fty), fname.span)?;
            let motive = cx.tc.mk_lam(&[t0], &fty_motive);
            let minor = cx.tc.mk_lam(&tele.fields, &fvar(tele.fields[j]));
            let rec = cnst(format!("{ind}.rec").as_str().into(), vec![lvl]);
            let mut args = tele.pargs();
            args.extend([motive, minor, fvar(s)]);
            let body = mk_apps(&rec, &args);
            let binders: Vec<u32> = tele.params.iter().copied().chain([s]).collect();
            let extra = tele.field_masks.get(j).cloned().unwrap_or_default();
            (
                cx.close(&binders, &fty, true, fname.span)?,
                cx.close(&binders, &body, false, fname.span)?,
                extra,
            )
        };
        let pname = Ident {
            name: format!("{ind}.{}", fname.name),
            span: fname.span,
        };
        let mut mask = vec![Bk::Imp; nparams];
        mask.push(last);
        mask.extend(extra);
        self.add_def(&pname, ty, val, mask)
    }

    // ---- traits and impls ----

    /// A trait becomes a one-constructor structure (the "dictionary") whose
    /// fields are the methods; each method is a projection that takes the
    /// instance as an instance-implicit argument.
    fn elab_trait(&mut self, d: &TraitDecl, span: Span) -> R<()> {
        let name = d.name.name.clone();
        if self.env.get(&name).is_some() {
            return err(d.name.span, format!("`{name}` is already declared"));
        }
        // a method with its own type parameters makes the field a `Π (B : Type), ..`,
        // which lives one universe higher
        let generic_methods = d
            .fns
            .iter()
            .any(|m| m.generics.iter().any(|g| !g.name.name.starts_with('\'')));
        let level = if generic_methods { 2 } else { 1 };
        let mut gens = vec![Generic {
            name: Ident {
                name: "Self".into(),
                span: d.name.span,
            },
            ty: None,
            out: false,
        }];
        gens.extend(d.generics.iter().cloned());
        let nparams = gens
            .iter()
            .filter(|g| !g.name.name.starts_with('\''))
            .count();
        let ind_ty = self.ind_type(&gens, level, span)?;
        let mut scratch = self.env.clone();
        from_kernel(scratch.add_axiom(&name, &[], ind_ty.clone()), d.name.span)?;
        let ctor_ty = {
            let mut cx = Cx::new(&scratch, &self.masks, &self.aliases, &self.tables);
            let tele = cx.trait_telescope(&gens, d)?;
            let result = mk_apps(&cnst(name.as_str().into(), vec![]), &tele.pargs());
            let all: Vec<u32> = tele.params.iter().chain(&tele.fields).copied().collect();
            cx.close(&all, &result, true, span)?
        };
        self.register_inductive(
            InductiveDecl {
                name: name.as_str().into(),
                lparams: vec![],
                nparams,
                ty: ind_ty,
                ctors: vec![(format!("{name}.mk").as_str().into(), ctor_ty)],
            },
            nparams,
            span,
        )?;
        for (j, m) in d.fns.iter().enumerate() {
            self.add_projection(&name, nparams, j, &m.name, Bk::Inst, &|cx| {
                cx.trait_telescope(&gens, d)
            })?;
        }
        let outer: Vec<String> = d
            .generics
            .iter()
            .filter(|g| g.name.name.starts_with('\''))
            .map(|g| g.name.name.clone())
            .collect();
        for m in &d.fns {
            let callee = callee_of(m, &outer).map_err(sig_error)?;
            self.tables
                .sigs
                .insert(format!("{name}.{}", m.name.name), callee);
        }
        let methods: Vec<String> = d.fns.iter().map(|m| m.name.name.clone()).collect();
        for m in &methods {
            self.tables
                .methods
                .entry(m.clone())
                .or_default()
                .push(name.clone());
        }
        let info = TraitInfo {
            nparams,
            outs: std::iter::once(false)
                .chain(
                    d.generics
                        .iter()
                        .filter(|g| !g.name.name.starts_with('\''))
                        .map(|g| g.out),
                )
                .collect(),
            methods,
            generics: d
                .generics
                .iter()
                .filter(|g| !g.name.name.starts_with('\''))
                .map(|g| g.name.name.clone())
                .collect(),
            defaults: d
                .fns
                .iter()
                .filter(|m| m.body.is_some())
                .map(|m| (m.name.name.clone(), m.clone()))
                .collect(),
        };
        self.tables.traits.insert(name, info);
        Ok(())
    }

    fn elab_impl(&mut self, d: &ImplDecl, span: Span) -> R<()> {
        match &d.trait_ref {
            Some(tr) => self.elab_trait_impl(d, tr, span),
            None => self.elab_inherent_impl(d, span),
        }
    }

    /// `impl<G> Trait<A> for Ty { fn .. }` becomes a definition
    /// `inst : Π G, Trait Ty A := Trait.mk Ty A (method terms)`.
    ///
    /// Methods are built one at a time; a method may use the ones built before it
    /// (through a provisional dictionary whose unbuilt fields are placeholders).
    /// Methods the impl omits take the trait's default body.
    fn elab_trait_impl(&mut self, d: &ImplDecl, tr: &Expr, span: Span) -> R<()> {
        let (trait_name, ty, val, mask) = {
            let mut cx = self.cx();
            let Some((tname, targs)) = cx.trait_ref(tr) else {
                return err(tr.span, "expected the name of a trait");
            };
            let info = self.tables.traits[&tname].clone();
            let (fvs, mask) = cx.elab_binders(&d.generics, &[])?;
            cx.outer_lifetimes = d
                .generics
                .iter()
                .filter(|g| g.name.name.starts_with('\''))
                .map(|g| g.name.name.clone())
                .collect();
            let self_ty = cx.elab_type(&d.self_ty)?;
            cx.scope.push(("Self".into(), self_ty.clone()));
            let mut class_args = vec![self_ty];
            for a in targs {
                class_args.push(cx.elab_type(a)?);
            }
            if class_args.len() != info.nparams {
                return err(
                    tr.span,
                    format!(
                        "trait `{tname}` takes {} type arguments (`Self` included), but {} were given",
                        info.nparams,
                        class_args.len()
                    ),
                );
            }
            let class_app = mk_apps(&cnst(tname.as_str().into(), vec![]), &class_args);
            let ctor = format!("{tname}.mk");
            let ctor_ty = from_kernel(self.env.const_type(&ctor, &[]), span)?;
            // field types, with placeholders standing for the methods not built yet
            let mut cur = from_kernel(cx.tc.instantiate_pis(&ctor_ty, &class_args), span)?;
            let (mut doms, mut holes) = (Vec::new(), Vec::new());
            for mname in &info.methods {
                let w = from_kernel(cx.tc.whnf(&cur), span)?;
                let Term::Pi(_, dom, body) = &*w else {
                    return err(span, "internal error: malformed trait structure");
                };
                let hole = cx.tc.fresh(&format!("<{mname}>"), dom.clone(), Mult::Omega);
                doms.push(dom.clone());
                holes.push(hole);
                cur = instantiate(body, &fvar(hole));
            }
            if let Some(extra) = d.fns.iter().find(|f| !info.methods.contains(&f.name.name)) {
                return err(
                    extra.name.span,
                    format!("`{}` is not a method of `{tname}`", extra.name.name),
                );
            }
            let n = info.methods.len();
            cx.pending = Some(Pending {
                trait_name: tname.clone(),
                class_args: class_args.clone(),
                built: vec![None; n],
                holes,
                methods: info.methods.clone(),
            });

            // the methods the impl writes, retrying those that need a later sibling
            let mut todo: Vec<usize> = (0..n)
                .filter(|&i| d.fns.iter().any(|f| f.name.name == info.methods[i]))
                .collect();
            while !todo.is_empty() {
                let mut progress = false;
                let mut first_err = None;
                for i in todo.clone() {
                    let f = d
                        .fns
                        .iter()
                        .find(|f| f.name.name == info.methods[i])
                        .expect("present");
                    let (depth, nlocal, ngoals) =
                        (cx.scope.len(), cx.local_insts.len(), cx.goals.len());
                    let snap = cx.tc.snapshot();
                    match cx.elab_method(f, &doms[i]) {
                        Ok(term) => {
                            cx.pending.as_mut().expect("pending").built[i] = Some(term);
                            todo.retain(|&j| j != i);
                            progress = true;
                        }
                        Err(e) if e.msg.contains(NOT_BUILT) => {
                            cx.scope.truncate(depth);
                            cx.local_insts.truncate(nlocal);
                            cx.goals.truncate(ngoals);
                            cx.tc.restore(snap);
                            first_err.get_or_insert(e);
                        }
                        Err(e) => return Err(e),
                    }
                }
                if !progress {
                    return Err(first_err.expect("an error was recorded"));
                }
            }

            // default bodies for the rest; they may name the trait's own parameters
            let depth = cx.scope.len();
            for (g, a) in info.generics.iter().zip(class_args.iter().skip(1)) {
                cx.scope.push((g.clone(), a.clone()));
            }
            for (i, (mname, dom)) in info.methods.iter().zip(&doms).enumerate() {
                if cx.pending.as_ref().expect("pending").built[i].is_some() {
                    continue;
                }
                let Some(f) = info.defaults.get(mname) else {
                    return err(
                        span,
                        format!("missing method `{mname}` in this impl of `{tname}`"),
                    );
                };
                let term = cx.elab_method(f, dom)?;
                cx.pending.as_mut().expect("pending").built[i] = Some(term);
            }
            cx.scope.truncate(depth);

            let terms: Vec<T> = cx
                .pending
                .take()
                .expect("pending")
                .built
                .into_iter()
                .map(|t| t.expect("all methods built"))
                .collect();
            let mut mk_args = class_args;
            mk_args.extend(terms);
            let value = mk_apps(&cnst(ctor.as_str().into(), vec![]), &mk_args);
            let ty = cx.close(&fvs, &class_app, true, span)?;
            let val = cx.close(&fvs, &value, false, span)?;
            (tname, ty, val, mask)
        };
        self.check_overlap(&trait_name, &ty, &mask, span)?;
        self.inst_counter += 1;
        let name = format!("inst_{trait_name}_{}", self.inst_counter);
        self.add_def(
            &Ident {
                name: name.clone(),
                span,
            },
            ty,
            val,
            mask,
        )?;
        self.tables.insts.entry(trait_name).or_default().push(name);
        Ok(())
    }

    /// Two impls of one trait may not apply to the same type.
    fn check_overlap(&self, trait_name: &str, ty: &T, mask: &[Bk], span: Span) -> R<()> {
        let Some(olds) = self.tables.insts.get(trait_name) else {
            return Ok(());
        };
        for old in olds {
            let mut cx = self.cx();
            let (_, r_new, _) = cx.open_binders(cnst("new".into(), vec![]), ty.clone(), mask)?;
            let (_, r_old, _) = cx.open_instance(old)?;
            if from_kernel(cx.tc.is_def_eq(&r_new, &r_old), span)? {
                return err(
                    span,
                    format!("this impl overlaps with an existing impl of `{trait_name}`"),
                );
            }
        }
        Ok(())
    }

    /// `impl Ty { fn m(..) }` defines `Ty.m`, callable as `x.m(..)`.
    fn elab_inherent_impl(&mut self, d: &ImplDecl, span: Span) -> R<()> {
        let head = {
            let mut cx = self.cx();
            cx.elab_binders(&d.generics, &[])?;
            let t = cx.elab_type(&d.self_ty)?;
            let w = from_kernel(cx.tc.whnf(&t), span)?;
            let (h, _) = app_spine(&w);
            match &*h {
                Term::Const(n, _) => n.to_string(),
                _ => {
                    return err(
                        d.self_ty.span,
                        "an impl needs a named type, like a struct or an enum",
                    )
                }
            }
        };
        for f in &d.fns {
            let mut generics = d.generics.clone();
            generics.extend(f.generics.iter().cloned());
            let fd = FnDecl {
                name: Ident {
                    name: format!("{head}.{}", f.name.name),
                    span: f.name.span,
                },
                generics,
                params: f.params.clone(),
                ret: f.ret.clone(),
                body: f.body.clone(),
                wf: None,
            };
            let callee = callee_of(&fd, &[]).map_err(sig_error)?;
            let (ty, val, mask) = self.try_fn(&fd, span, None, false, Some(&d.self_ty))?;
            let kname = self.add_def_named(&fd.name, ty, val, mask)?;
            self.tables.sigs.insert(kname, callee);
        }
        Ok(())
    }
}

#[derive(Clone)]
enum Pat {
    Wild,
    Var(String),
    Ctor(String, Vec<Pat>),
}

struct Row<'e> {
    pats: Vec<Pat>,
    binds: Vec<(String, T)>,
    body: &'e Expr,
}

/// A `by { .. }` term: the proof is built once its type has no unknowns left.
struct PendingBy {
    mv: T,
    tactics: Vec<Tactic>,
    scope: Vec<(String, T)>,
    span: Span,
}

/// State for elaborating a structurally recursive function.
struct RecCtx {
    name: String,
    /// The decreasing parameter.
    decr: u32,
    /// All explicit parameters, in order.
    explicit: Vec<u32>,
    /// Recursive fields of the top-level match on `decr`, with their induction hypotheses.
    fields: HashMap<u32, T>,
    /// A field variable that a nested `match` replaced by a constructor
    /// application, so recursive calls on it can still be recognized.
    refined: Vec<(T, u32)>,
    in_top: bool,
    /// Course-of-values mode (`brecOn`), for recursion on deeper subterms.
    deep: Option<Deep>,
    /// Well-founded recursion (`termination_by`).
    wf: Option<wf::WfCtx>,
    /// A function of a `mutual` group of structurally recursive functions.
    mutual: Option<MutualCtx>,
}

/// The other functions of a mutually recursive group and the motives of the shared recursor.
#[derive(Clone)]
struct MutualCtx {
    /// Name and number of arguments of each function.
    siblings: Vec<(String, usize)>,
    /// One motive per member of the family (types, then nested occurrences), over this
    /// function's type parameters.
    motives: Vec<T>,
    /// Set for the function on a nested occurrence (`List<Rose>`).
    view: Option<AuxView>,
}

/// How a function on a nested occurrence sees its family.
#[derive(Clone)]
struct AuxView {
    /// Index among the family's nested occurrences.
    nested_idx: usize,
    /// The family's first type (its `IndInfo` lists the family and the nested occurrences).
    root: String,
    fam_params: Vec<T>,
    fam_levels: Vec<Level>,
}

/// State of a function compiled through `I.brecOn`: every recursive field in scope
/// has a term of type `I.below motive field`, a tuple of the results for its subterms.
#[derive(Clone)]
struct Deep {
    iname: String,
    /// Universe arguments of `I.below` / `I.brecOn`: the motive's, then `I`'s.
    levels: Vec<Level>,
    params: Vec<T>,
    motive: T,
    /// The `below` argument of `brecOn`'s step function.
    b: u32,
    below_of: HashMap<u32, T>,
}

struct StructTele {
    params: Vec<u32>,
    fields: Vec<u32>,
    field_tys: Vec<T>,
    field_names: Vec<String>,
    /// Binder kinds of each field's own leading generics (trait methods only).
    field_masks: Vec<Vec<Bk>>,
}

impl StructTele {
    fn pargs(&self) -> Vec<T> {
        self.params.iter().map(|&i| fvar(i)).collect()
    }
}

/// Per-declaration elaboration context.
struct Cx<'a> {
    tc: TypeChecker<'a>,
    env: &'a Env,
    masks: &'a Masks,
    aliases: &'a Aliases,
    tables: &'a Tables,
    /// Instance arguments waiting for their types to become known.
    goals: Vec<(T, Span)>,
    /// `by { .. }` terms waiting for their expected type to be known.
    pending_by: Vec<PendingBy>,
    /// Instance variables in scope (from `T: Trait` bounds).
    local_insts: Vec<T>,
    scope: Vec<(String, T)>,
    rec: Option<RecCtx>,
    pending: Option<Pending>,
    /// Bindings produced by effects (assignments, `&mut` calls) that the enclosing
    /// binder must wrap around its result.
    lets: Vec<(u32, T, T)>,
    /// Set while compiling the arms of a `match` that threads mutable variables.
    stateful: Option<StateCtx>,
    /// The next `if`/`match` is a statement of a `do` block: its branches are `do` blocks.
    do_mode: bool,
    /// Same, for the arms of the `match` being compiled.
    leaf_do: bool,
    synth_counter: usize,
    /// Where each call was resolved to a constant, for the borrow checker.
    calls: HashMap<(u32, u32), String>,
    /// `&T` parameters (the variable ids), which cannot be assigned through.
    shared_refs: Vec<u32>,
    /// Lifetimes declared by the enclosing impl.
    outer_lifetimes: Vec<String>,
    /// Where each metavariable was created, for "cannot infer" errors.
    spans: HashMap<u32, Span>,
    /// `if` branches get the condition as a hypothesis (needed by `decreasing_by`).
    dep_if: bool,
    /// The call being unfolded by `simp` (so its recursive calls can be folded back).
    pending_call: T,
    /// Binder names per constructor for the cases of a dependent `match`.
    case_names: Option<HashMap<String, Vec<String>>>,
    /// Minor premises of the top-level `match` of a function in a `mutual` group.
    mutual_minors: Vec<(String, T)>,
}

fn path_name(e: &Expr) -> Option<String> {
    match &e.kind {
        ExprKind::Var(n) => Some(n.clone()),
        ExprKind::Field(b, f) => path_name(b).map(|p| format!("{p}.{}", f.name)),
        _ => None,
    }
}

impl<'a> Cx<'a> {
    fn new(env: &'a Env, masks: &'a Masks, aliases: &'a Aliases, tables: &'a Tables) -> Self {
        Cx {
            tc: TypeChecker::new(env),
            env,
            masks,
            aliases,
            tables,
            goals: Vec::new(),
            pending_by: Vec::new(),
            local_insts: Vec::new(),
            scope: Vec::new(),
            rec: None,
            pending: None,
            lets: Vec::new(),
            stateful: None,
            do_mode: false,
            leaf_do: false,
            synth_counter: 0,
            calls: HashMap::new(),
            shared_refs: Vec::new(),
            outer_lifetimes: Vec::new(),
            spans: HashMap::new(),
            dep_if: false,
            pending_call: lit(0),
            case_names: None,
            mutual_minors: Vec::new(),
        }
    }

    fn unit_type(&self) -> T {
        cnst("Unit".into(), vec![])
    }

    fn unit_value(&self) -> T {
        cnst("Unit.unit".into(), vec![])
    }

    fn new_mvar(&mut self, ty: T, span: Span) -> T {
        let m = self.tc.new_mvar(ty);
        if let Term::MVar(id) = &*m {
            self.spans.insert(*id, span);
        }
        m
    }

    fn pp(&self, t: &T) -> String {
        self.tc.pp(&self.tc.zonk(t))
    }

    // ---- binders ----

    fn is_sort(&mut self, ty: &T) -> bool {
        matches!(self.tc.whnf(ty).as_deref(), Ok(Term::Sort(_)))
    }

    /// Introduce generics (implicit, erased when they are types) and parameters.
    fn elab_binders(&mut self, generics: &[Generic], params: &[Param]) -> R<(Vec<u32>, Vec<Bk>)> {
        let mut fvs = Vec::new();
        let mut mask = Vec::new();
        for g in generics {
            if g.name.name.starts_with('\'') {
                continue; // lifetimes are handled by the borrow checker
            }
            let bounds = match &g.ty {
                Some(t) => self.bound_list(t)?,
                None => None,
            };
            let ty = match (&g.ty, &bounds) {
                (Some(t), None) => self.elab_type(t)?,
                _ => sort(Level::of_nat(1)),
            };
            let mult = if self.is_sort(&ty) {
                Mult::Zero
            } else {
                Mult::Omega
            };
            let id = self.tc.fresh(&g.name.name, ty, mult);
            self.scope.push((g.name.name.clone(), fvar(id)));
            fvs.push(id);
            mask.push(Bk::Imp);
            // `T: Trait` adds a dictionary parameter, found by instance search at call sites
            for (tn, targs) in bounds.into_iter().flatten() {
                let mut cargs = vec![fvar(id)];
                for a in targs {
                    cargs.push(self.elab_type(a)?);
                }
                let cty = mk_apps(&cnst(tn.as_str().into(), vec![]), &cargs);
                let d = self.tc.fresh("inst", cty, Mult::Omega);
                fvs.push(d);
                mask.push(Bk::Inst);
                self.local_insts.push(fvar(d));
            }
        }
        for p in params {
            let ty = self.elab_type(&p.ty)?;
            let mult = match p.mode {
                Mode::Own => Mult::One,
                Mode::Default if self.is_sort(&ty) => Mult::Zero,
                Mode::Default => Mult::Omega,
            };
            let id = self.tc.fresh(&p.name.name, ty, mult);
            if matches!(p.ty.kind, ExprKind::Ref { mutable: false, .. }) {
                self.shared_refs.push(id);
            }
            let key = if matches!(p.ty.kind, ExprKind::Ref { mutable: true, .. }) {
                mut_key(&p.name.name)
            } else {
                p.name.name.clone()
            };
            self.scope.push((key, fvar(id)));
            fvs.push(id);
            mask.push(Bk::Exp);
        }
        Ok((fvs, mask))
    }

    fn struct_telescope(&mut self, d: &StructDecl) -> R<StructTele> {
        let (params, _) = self.elab_binders(&d.generics, &[])?;
        let mut fields = Vec::new();
        let mut field_tys = Vec::new();
        for f in &d.fields {
            let ty = self.elab_type(&f.ty)?;
            self.solve_goals(true)?;
            self.tc.zonk_locals();
            let ty = self.tc.zonk(&ty);
            let id = self.tc.fresh(&f.name.name, ty.clone(), Mult::Omega);
            self.scope.push((f.name.name.clone(), fvar(id)));
            fields.push(id);
            field_tys.push(ty);
        }
        Ok(StructTele {
            params,
            fields,
            field_tys,
            field_names: d.fields.iter().map(|f| f.name.name.clone()).collect(),
            field_masks: vec![],
        })
    }

    /// Zonk and abstract `fvs` over `body`; fails if metavariables remain.
    fn close(&mut self, fvs: &[u32], body: &T, is_pi: bool, span: Span) -> R<T> {
        self.solve_goals(true)?;
        self.tc.zonk_locals();
        let body = if is_pi {
            body.clone()
        } else {
            self.wrap_lets(0, body.clone())
        };
        let body = self.tc.zonk(&body);
        let body = self.devirt(&body);
        let t = self.tc.mk_binding(fvs, &body, is_pi);
        if let Some(m) = first_mvar(&t) {
            let at = self.spans.get(&m).copied().unwrap_or(span);
            return err(
                at,
                "cannot infer this placeholder or implicit argument; add a type annotation",
            );
        }
        if has_level_mvar(&t) {
            return err(span, "cannot infer a universe level; add a type annotation");
        }
        Ok(t)
    }

    // ---- name resolution ----

    fn resolve(&self, name: &str) -> Option<Res> {
        if let Some(i) = self.lookup_scope(name) {
            return Some(Res::Local(self.scope[i].1.clone()));
        }
        for cand in self.name_candidates(name) {
            if let Some(k) = self.tables.shadow.get(&cand) {
                return Some(Res::Global(k.clone()));
            }
            if self.env.get(&cand).is_some() {
                return Some(Res::Global(cand));
            }
            if let Some(full) = self.aliases.get(&cand) {
                return Some(Res::Global(full.clone()));
            }
        }
        None
    }

    /// The names a source name can stand for, best first: inside `namespace A.B`
    /// `x` may be `A.B.x` or `A.x`, then names of `open`ed namespaces, then `x` itself.
    fn name_candidates(&self, name: &str) -> Vec<String> {
        let mut out = Vec::new();
        let ns = &self.tables.ns;
        for i in (1..=ns.len()).rev() {
            out.push(format!("{}.{name}", ns[..i].join(".")));
        }
        for o in self.tables.opens.iter().rev() {
            out.push(format!("{o}.{name}"));
        }
        out.push(name.to_string());
        out
    }

    /// A constant applied to fresh universe level metavariables.
    fn const_term(&mut self, name: &str) -> (T, Vec<Bk>) {
        let n = match self.env.get(name) {
            Some(d) => d.lparams().len(),
            None => 0,
        };
        let levels = (0..n).map(|_| self.tc.new_level_mvar()).collect();
        (
            cnst(name.into(), levels),
            self.masks.get(name).cloned().unwrap_or_default(),
        )
    }

    fn head_of(&mut self, path: &str) -> Option<(T, Vec<Bk>)> {
        match path {
            "Type" => return Some((sort(Level::of_nat(1)), vec![])),
            "Prop" => return Some((sort(Level::zero()), vec![])),
            _ => {}
        }
        match self.resolve(path)? {
            Res::Local(t) => Some((t, vec![])),
            Res::Global(n) => Some(self.const_term(&n)),
        }
    }

    // ---- expressions ----

    fn elab_type(&mut self, e: &Expr) -> R<T> {
        let t = self.elab(e, None)?;
        let ty = from_kernel(self.tc.infer(&t), e.span)?;
        match from_kernel(self.tc.ensure_sort(&ty), e.span) {
            Ok(_) => Ok(t),
            Err(_) => err(e.span, format!("expected a type, found `{}`", self.pp(&t))),
        }
    }

    fn elab_check(&mut self, e: &Expr, expected: &T) -> R<T> {
        let t = self.elab(e, Some(expected))?;
        self.coerce(t, expected, e.span)
    }

    /// Check that `t` has type `expected`.
    fn coerce(&mut self, t: T, expected: &T, span: Span) -> R<T> {
        let ty = from_kernel(self.tc.infer(&t), span)?;
        if from_kernel(self.tc.is_def_eq(&ty, expected), span)? {
            Ok(t)
        } else if let Some(c) = self.try_coe(&t, &ty, expected, span)? {
            Ok(c)
        } else {
            err(
                span,
                format!(
                    "type mismatch: expected `{}`, found `{}`",
                    self.pp(expected),
                    self.pp(&ty)
                ),
            )
        }
    }

    /// `Coe.coe t` when the program declares `impl Coe<B> for A` for the two types.
    fn try_coe(&mut self, t: &T, ty: &T, expected: &T, span: Span) -> R<Option<T>> {
        if !self.tables.traits.contains_key("Coe") {
            return Ok(None);
        }
        let (a, b) = (self.tc.zonk(ty), self.tc.zonk(expected));
        if first_mvar(&a).is_some() || first_mvar(&b).is_some() {
            return Ok(None);
        }
        let class_app = mk_apps(&cnst("Coe".into(), vec![]), &[a.clone(), b.clone()]);
        let Some(inst) = self.synth(&class_app, 0, span)? else {
            return Ok(None);
        };
        let f = cnst("Coe.coe".into(), vec![]);
        Ok(Some(mk_apps(&f, &[a, b, inst, t.clone()])))
    }

    /// A universe level expression: `u`, `3`, `u + 1`, `max(u, v)`, `imax(u, v)`.
    fn elab_level(&self, e: &Expr) -> R<Level> {
        match &e.kind {
            ExprKind::Nat(n) => Ok(Level::of_nat(*n as u32)),
            ExprKind::Var(n) if self.tables.universes.contains(n) => Ok(Level::param(n)),
            ExprKind::Var(n) => err(
                e.span,
                format!("unknown universe `{n}` (declare it with `universe {n};`)"),
            ),
            ExprKind::Binary(BinOp::Add, a, b) => {
                let base = self.elab_level(a)?;
                match &b.kind {
                    ExprKind::Nat(k) => Ok((0..*k).fold(base, |l, _| l.succ())),
                    _ => err(b.span, "a universe level can only be increased by a number"),
                }
            }
            ExprKind::Call(f, args) if args.len() == 2 => match &f.kind {
                ExprKind::Var(n) if n == "max" => Ok(Level::max(
                    self.elab_level(&args[0])?,
                    self.elab_level(&args[1])?,
                )),
                ExprKind::Var(n) if n == "imax" => Ok(Level::imax(
                    self.elab_level(&args[0])?,
                    self.elab_level(&args[1])?,
                )),
                _ => err(e.span, "expected a universe level"),
            },
            _ => err(e.span, "expected a universe level"),
        }
    }

    fn nat_literal(&self, n: u128, _span: Span) -> R<T> {
        Ok(lit(n))
    }

    fn elab(&mut self, e: &Expr, exp: Option<&T>) -> R<T> {
        match &e.kind {
            ExprKind::Var(_) | ExprKind::Field(..) => {
                if let Some(path) = path_name(e) {
                    if self.is_rec_name(&path) {
                        return err(
                            e.span,
                            "a recursive function must be called with all of its arguments",
                        );
                    }
                    if let Some(head) = self.head_of(&path) {
                        return self.elab_app(head, vec![], exp, e.span);
                    }
                }
                match &e.kind {
                    ExprKind::Field(base, f) => self.elab_field(base, f, exp, e.span),
                    ExprKind::Var(n) => err(e.span, format!("unknown identifier `{n}`")),
                    _ => unreachable!(),
                }
            }
            ExprKind::Nat(n) => self.nat_literal(*n, e.span),
            ExprKind::Unit => Ok(self.unit_value()),
            ExprKind::Wild => {
                let ty = match exp {
                    Some(t) => t.clone(),
                    None => {
                        let l = self.tc.new_level_mvar();
                        self.new_mvar(sort(l), e.span)
                    }
                };
                Ok(self.new_mvar(ty, e.span))
            }
            ExprKind::Binary(op, l, r) => {
                // `a + b` is `Add.add(a, b)`, and so on
                let (name, swap) = match op {
                    BinOp::Eq => ("Eq", false),
                    BinOp::Add => ("Add.add", false),
                    BinOp::Sub => ("Sub.sub", false),
                    BinOp::Mul => ("Mul.mul", false),
                    BinOp::EqEq => ("BEq.beq", false),
                    BinOp::Lt => ("Ord.lt", false),
                    BinOp::Gt => ("Ord.lt", true),
                    BinOp::Div => ("Div.div", false),
                    BinOp::Rem => ("Rem.rem", false),
                };
                let head = self.const_term(name);
                let args = if swap {
                    vec![Arg::Expr(r), Arg::Expr(l)]
                } else {
                    vec![Arg::Expr(l), Arg::Expr(r)]
                };
                self.elab_app(head, args, exp, e.span)
            }
            ExprKind::Arrow(a, b) => {
                let a = self.elab_type(a)?;
                let b = self.elab_type(b)?;
                Ok(pi(Mult::Omega, a, b))
            }
            ExprKind::Forall(binders, body) => {
                let depth = self.scope.len();
                let mut fvs = Vec::new();
                for (n, t) in binders {
                    let ty = self.elab_type(t)?;
                    let fv = self.tc.fresh(&n.name, ty, Mult::Omega);
                    self.scope.push((n.name.clone(), fvar(fv)));
                    fvs.push(fv);
                }
                let b = self.elab_type(body);
                self.scope.truncate(depth);
                let b = b?;
                self.tc.zonk_locals();
                let b = self.tc.zonk(&b);
                Ok(self.tc.mk_pi(&fvs, &b))
            }
            ExprKind::Call(f, args) | ExprKind::TypeApp(f, args) => {
                // `Type(u)` is `Sort (u+1)`, `Sort(u)` the sort itself
                if let (ExprKind::Var(n), [lv]) = (&f.kind, args.as_slice()) {
                    if (n == "Type" || n == "Sort") && self.lookup_scope(n).is_none() {
                        let l = self.elab_level(lv)?;
                        return Ok(sort(if n == "Type" { l.succ() } else { l }));
                    }
                }
                if let Some(p) = path_name(f) {
                    if self.is_rec_name(&p) {
                        return self.elab_rec_call(&p, args, exp, e.span);
                    }
                }
                let head = match path_name(f).and_then(|p| self.head_of(&p)) {
                    Some(h) => h,
                    None if matches!(f.kind, ExprKind::Var(_)) => {
                        let ExprKind::Var(n) = &f.kind else {
                            unreachable!()
                        };
                        return err(f.span, format!("unknown identifier `{n}`"));
                    }
                    None if matches!(f.kind, ExprKind::Field(..)) => {
                        let ExprKind::Field(base, m) = &f.kind else {
                            unreachable!()
                        };
                        return self.elab_method_call(base, m, args, exp, e.span);
                    }
                    None => (self.elab(f, None)?, vec![]),
                };
                self.elab_app(head, args.iter().map(Arg::Expr).collect(), exp, e.span)
            }
            ExprKind::Block(b) => self.elab_block_opts(b, exp, true),
            // references are values: `*r` is `r`
            ExprKind::Deref(inner) => self.elab(inner, exp),
            ExprKind::By(tactics) => {
                let Some(ty) = exp else {
                    return err(
                        e.span,
                        "a `by` block needs a known expected type; use `have` or add an annotation",
                    );
                };
                let mv = self.new_mvar(ty.clone(), e.span);
                self.pending_by.push(PendingBy {
                    mv: mv.clone(),
                    tactics: tactics.clone(),
                    scope: self.scope.clone(),
                    span: e.span,
                });
                Ok(mv)
            }
            ExprKind::Ascribe(inner, ty) => {
                let ty = self.elab_type(ty)?;
                self.solve_goals(false)?;
                let ty = self.tc.zonk(&ty);
                self.elab_check(inner, &ty)
            }
            ExprKind::Do(b) => self.elab_do(b, exp, e.span),
            ExprKind::For { var, iter, body } => self.elab_for(var, iter, body, e.span),
            ExprKind::Lambda { params, body } => self.elab_lambda(params, body, exp, e.span),
            ExprKind::List(items) => {
                // [a, b] is List.cons(a, List.cons(b, List.nil))
                let var = |n: &str, span| Expr {
                    kind: ExprKind::Var(n.into()),
                    span,
                };
                let mut list = var("List.nil", e.span);
                for it in items.iter().rev() {
                    list = Expr {
                        kind: ExprKind::Call(
                            Box::new(var("List.cons", it.span)),
                            vec![it.clone(), list],
                        ),
                        span: e.span,
                    };
                }
                self.elab(&list, exp)
            }
            ExprKind::If(cond, then, els) => self.elab_if(cond, then, els.as_deref(), exp, e.span),
            // references are not tracked yet: `&x` elaborates as `x` (the borrow checker is M5)
            ExprKind::Ref { inner, .. } => self.elab(inner, exp),
            ExprKind::Match(scrut, arms) => self.elab_match(scrut, arms, exp, e.span),
            ExprKind::Neg(inner) => {
                // `-x` is `Neg.neg(x)`
                let call = Expr {
                    kind: ExprKind::Call(
                        Box::new(Expr {
                            kind: ExprKind::Var("Neg.neg".into()),
                            span: e.span,
                        }),
                        vec![(**inner).clone()],
                    ),
                    span: e.span,
                };
                self.elab(&call, exp)
            }
            ExprKind::Str(text) => Ok(str_lit(text)),
        }
    }

    fn elab_field(&mut self, base: &Expr, f: &Ident, exp: Option<&T>, span: Span) -> R<T> {
        let b = self.elab(base, None)?;
        let bt = from_kernel(self.tc.infer(&b), base.span)?;
        let bt = from_kernel(self.tc.whnf(&bt), base.span)?;
        let (h, _) = app_spine(&bt);
        let Term::Const(sname, _) = &*h else {
            return err(
                f.span,
                format!("no field `{}` on type `{}`", f.name, self.pp(&bt)),
            );
        };
        let proj = format!("{sname}.{}", f.name);
        if !matches!(self.env.get(&proj), Some(Decl::Def { .. })) {
            return err(f.span, format!("type `{sname}` has no field `{}`", f.name));
        }
        let head = self.const_term(&proj);
        self.elab_app(head, vec![Arg::Term(b)], exp, span)
    }

    /// Apply `head` to `args`, inserting implicit arguments as metavariables.
    fn elab_app(
        &mut self,
        head: (T, Vec<Bk>),
        args: Vec<Arg<'_>>,
        exp: Option<&T>,
        span: Span,
    ) -> R<T> {
        let (mut term, mask) = head;
        let sig = match &*app_spine(&term).0 {
            Term::Const(n, _) => {
                self.calls.insert((span.start, span.end), n.to_string());
                self.tables.sigs.get(&**n).cloned()
            }
            _ => None,
        };
        let takes_mut = |k: usize| {
            sig.as_ref().and_then(|s| s.params.get(k)).copied() == Some(ParamKind::RefMut)
        };
        let has_mut = sig.as_ref().is_some_and(Callee::has_mut_params);
        let mut fty = from_kernel(self.tc.infer(&term), span)?;
        let mut pending: Vec<(T, usize)> = Vec::new();
        let (mut next, mut i) = (0, 0);
        loop {
            let w = from_kernel(self.tc.whnf(&fty), span)?;
            match &*w {
                Term::Pi(_, d, b) => {
                    let kind = mask.get(i).copied().unwrap_or(Bk::Exp);
                    if kind == Bk::Exp && next >= args.len() {
                        break;
                    }
                    let mv = self.new_mvar(d.clone(), span);
                    term = app(term, mv.clone());
                    fty = instantiate(b, &mv);
                    i += 1;
                    match kind {
                        Bk::Exp => {
                            pending.push((mv, next));
                            next += 1;
                        }
                        Bk::Imp => {}
                        Bk::Inst => self.goals.push((mv, span)),
                    }
                }
                _ => {
                    if next < args.len() {
                        return err(
                            span,
                            format!("too many arguments: `{}` is not a function", self.pp(&term)),
                        );
                    }
                    break;
                }
            }
        }
        // use the expected type to solve implicit arguments before elaborating the explicit ones
        if has_mut && sig.as_ref().is_some_and(|s| args.len() < s.params.len()) {
            return err(
                span,
                "a function with `&mut` parameters cannot be partially applied",
            );
        }
        // (a function with `&mut` parameters returns a pair, not the value `exp` describes)
        if let (Some(exp), true, false) = (exp, next == args.len(), has_mut) {
            let snap = self.tc.snapshot();
            if !from_kernel(self.tc.is_def_eq(&fty, exp), span)? {
                self.tc.restore(snap);
            }
        }
        let mut mut_places: Vec<Place> = Vec::new();
        for (mv, k) in pending {
            let dom = from_kernel(self.tc.infer(&mv), span)?;
            let dom = self.tc.zonk(&dom);
            let a = match &args[k] {
                Arg::Expr(e) if takes_mut(k) => {
                    let (pl, cur) = self.mut_arg(e)?;
                    mut_places.push(pl);
                    self.coerce(cur, &dom, e.span)?
                }
                Arg::Recv(_, base) if takes_mut(k) => {
                    let pl = self.receiver_place(base)?;
                    let (cur, _) = self.read_place(&pl, base.span)?;
                    mut_places.push(pl);
                    self.coerce(cur, &dom, base.span)?
                }
                Arg::Expr(e) => self.elab_check(e, &dom)?,
                Arg::Term(t) | Arg::Recv(t, _) => self.coerce(t.clone(), &dom, span)?,
            };
            if !from_kernel(self.tc.is_def_eq(&mv, &a), span)? {
                return err(
                    span,
                    format!(
                        "argument `{}` does not match the expected `{}`",
                        self.pp(&a),
                        self.pp(&mv)
                    ),
                );
            }
        }
        if !mut_places.is_empty() {
            // the call returned `(result, updated &mut arguments)`: bind it, and
            // give each borrowed place its updated value
            let rty = self.tc.zonk(&fty);
            let rty = from_kernel(self.tc.whnf(&rty), span)?;
            let (h, targs) = app_spine(&rty);
            if !matches!(&*h, Term::Const(n, _) if &**n == "Prod") || targs.len() != 2 {
                return err(
                    span,
                    "internal error: a function with `&mut` parameters must return a pair",
                );
            }
            let (r_ty, s_ty) = (targs[0].clone(), targs[1].clone());
            let tys = split_tuple_ty(&s_ty, mut_places.len());
            let p = self.tc.fresh("call", rty.clone(), Mult::Omega);
            self.lets.push((p, rty.clone(), term));
            let snd = prod_snd(&r_ty, &s_ty, fvar(p));
            for (i, pl) in mut_places.iter().enumerate() {
                let updated = tuple_get(&tys, snd.clone(), i);
                self.assign_place(pl, updated, span)?;
            }
            self.solve_goals(false)?;
            return Ok(prod_fst(&r_ty, &s_ty, fvar(p)));
        }
        self.solve_goals(false)?;
        Ok(term)
    }

    /// The place behind an argument passed to a `&mut` parameter: `&mut place`,
    /// or a place that is itself a `&mut` variable (an implicit reborrow).
    fn mut_arg(&mut self, e: &Expr) -> R<(Place, T)> {
        let place_expr = match &e.kind {
            ExprKind::Ref {
                mutable: true,
                inner,
                ..
            } => &**inner,
            ExprKind::Ref { mutable: false, .. } => {
                return err(
                    e.span,
                    "this parameter takes `&mut`, but a shared reference `&` was given",
                )
            }
            _ if is_place_expr(e) => e,
            _ => return err(e.span, "this parameter takes `&mut`: pass `&mut place`"),
        };
        let pl = self.resolve_place(place_expr, "borrow as mutable")?;
        let (cur, _) = self.read_place(&pl, e.span)?;
        Ok((pl, cur))
    }

    /// `base.method(..)` where the method takes `&mut self`: `base` must be a place.
    fn receiver_place(&mut self, base: &Expr) -> R<Place> {
        if !is_place_expr(base) {
            return err(
                base.span,
                "cannot call a `&mut self` method on a temporary value; store it in a `let mut` variable first",
            );
        }
        self.resolve_place(base, "borrow as mutable")
    }

    /// Borrow-check the function `f` that was just elaborated.
    fn borrow_check(&self, f: &FnDecl) -> R<()> {
        let callee = callee_of(f, &self.outer_lifetimes).map_err(sig_error)?;
        let resolver = |sp: Span| {
            self.calls
                .get(&(sp.start, sp.end))
                .and_then(|n| self.tables.sigs.get(n))
                .cloned()
        };
        let is_ctor = |n: &str| self.global_ctor(n).is_some();
        match apex_borrowck::check_fn(f, &callee, &resolver, &is_ctor)
            .into_iter()
            .next()
        {
            Some(d) => Err(borrow_error(d)),
            None => Ok(()),
        }
    }

    /// The `&mut` parameters of a function, as mutable variables.
    fn mut_params(&self, params: &[Param]) -> Vec<(String, usize)> {
        params
            .iter()
            .filter(|p| matches!(p.ty.kind, ExprKind::Ref { mutable: true, .. }))
            .filter_map(|p| {
                self.lookup_scope(&p.name.name)
                    .map(|i| (p.name.name.clone(), i))
            })
            .collect()
    }

    /// What a function with `&mut` parameters returns: `(result, updated parameters)`.
    fn with_mut_result(&mut self, ret: &T, vars: &[(String, usize)]) -> R<T> {
        if vars.is_empty() {
            return Ok(ret.clone());
        }
        let tys = self.state_types(vars)?;
        Ok(prod_ty(ret, &tuple_ty(&tys)))
    }

    /// The body's value together with the `&mut` parameters as the body leaves them.
    fn wrap_mut_result(&mut self, ret: &T, vars: &[(String, usize)], v: T) -> R<T> {
        if vars.is_empty() {
            return Ok(v);
        }
        let tys = self.state_types(vars)?;
        let cur = self.state_terms(vars);
        Ok(prod_mk(ret, &tuple_ty(&tys), v, tuple_mk(&tys, &cur)))
    }

    // ---- traits: bounds, instance search, methods ----

    /// `Trait` or `Trait<A, ..>` naming a declared trait.
    fn trait_ref<'e>(&self, e: &'e Expr) -> Option<(String, &'e [Expr])> {
        let (head, args): (&Expr, &[Expr]) = match &e.kind {
            ExprKind::TypeApp(f, args) | ExprKind::Call(f, args) => (f, args.as_slice()),
            _ => (e, &[]),
        };
        let p = path_name(head)?;
        if self.scope.iter().any(|(n, _)| *n == p) {
            return None; // a variable shadows the trait name
        }
        self.tables.traits.contains_key(&p).then_some((p, args))
    }

    /// The traits in a bound like `Show + Eq`, or `None` if `e` is an ordinary
    /// type annotation.
    fn bound_list<'e>(&self, e: &'e Expr) -> R<Option<Vec<Bound<'e>>>> {
        let mut parts = Vec::new();
        flatten_add(e, &mut parts);
        let refs: Vec<_> = parts.iter().map(|p| self.trait_ref(p)).collect();
        if refs.iter().all(Option::is_none) {
            return Ok(None);
        }
        if refs.iter().any(Option::is_none) {
            return err(e.span, "a bound may only mention traits");
        }
        Ok(Some(refs.into_iter().flatten().collect()))
    }

    fn trait_telescope(&mut self, gens: &[Generic], d: &TraitDecl) -> R<StructTele> {
        let (params, _) = self.elab_binders(gens, &[])?;
        let mut fields = Vec::new();
        let mut field_tys = Vec::new();
        let mut field_masks = Vec::new();
        for m in &d.fns {
            let (depth, nlocal) = (self.scope.len(), self.local_insts.len());
            let (pf, mask) = self.elab_binders(&m.generics, &m.params)?;
            let ret = match &m.ret {
                Some(t) => self.elab_type(t)?,
                None => self.unit_type(),
            };
            let mvars = self.mut_params(&m.params);
            let ret = self.with_mut_result(&ret, &mvars)?;
            let fty = self.close(&pf, &ret, true, m.name.span)?;
            self.scope.truncate(depth);
            self.local_insts.truncate(nlocal);
            let id = self.tc.fresh(&m.name.name, fty.clone(), Mult::Omega);
            fields.push(id);
            field_tys.push(fty);
            field_masks.push(mask);
        }
        Ok(StructTele {
            params,
            fields,
            field_tys,
            field_names: d.fns.iter().map(|m| m.name.name.clone()).collect(),
            field_masks,
        })
    }

    /// Elaborate an impl method as a term of type `expected`.
    fn elab_method(&mut self, f: &FnDecl, expected: &T) -> R<T> {
        let Some(block) = &f.body else {
            return err(f.name.span, "a method in an impl needs a body");
        };
        let (depth, nlocal) = (self.scope.len(), self.local_insts.len());
        let (pf, _) = self.elab_binders(&f.generics, &f.params)?;
        let ret = match &f.ret {
            Some(t) => self.elab_type(t)?,
            None => self.unit_type(),
        };
        let mvars = self.mut_params(&f.params);
        let ret_full = self.with_mut_result(&ret, &mvars)?;
        let body = self.scoped(|cx| {
            let v = cx.elab_block_opts(block, Some(&ret), true)?;
            let v = cx.coerce(v, &ret, block.span)?;
            cx.wrap_mut_result(&ret, &mvars, v)
        })?;
        self.borrow_check(f)?;
        let ty = self.close(&pf, &ret_full, true, f.name.span)?;
        if !from_kernel(self.tc.is_def_eq(&ty, expected), f.name.span)? {
            return err(
                f.name.span,
                format!(
                    "method `{}` has type `{}`, but the trait requires `{}`",
                    f.name.name,
                    self.pp(&ty),
                    self.pp(expected)
                ),
            );
        }
        let term = self.close(&pf, &body, false, f.name.span)?;
        self.scope.truncate(depth);
        self.local_insts.truncate(nlocal);
        // placeholders must not survive: they stand for methods not built yet
        if let Some(p) = &self.pending {
            for (j, &h) in p.holes.iter().enumerate() {
                if contains_fvar(&term, h) {
                    return err(
                        f.name.span,
                        format!(
                            "method `{}` of this impl {NOT_BUILT} (an impl cannot refer to itself as a whole)",
                            p.methods[j]
                        ),
                    );
                }
            }
        }
        Ok(term)
    }

    /// Open the leading binders of `fty` (a constant applied to `term` so far)
    /// as metavariables, returning the instance-binder metavariables separately.
    fn open_binders(&mut self, mut term: T, mut fty: T, mask: &[Bk]) -> R<(T, T, Vec<T>)> {
        let mut subgoals = Vec::new();
        let mut i = 0;
        loop {
            let w = from_kernel(self.tc.whnf(&fty), Span::default())?;
            let Term::Pi(_, d, b) = &*w else {
                return Ok((term, w, subgoals));
            };
            if i >= mask.len() {
                return Ok((term, w.clone(), subgoals));
            }
            let mv = self.new_mvar(d.clone(), Span::default());
            if mask[i] == Bk::Inst {
                subgoals.push(mv.clone());
            }
            term = app(term, mv.clone());
            fty = instantiate(b, &mv);
            i += 1;
        }
    }

    fn open_instance(&mut self, name: &str) -> R<(T, T, Vec<T>)> {
        let (t, mask) = self.const_term(name);
        let fty = from_kernel(self.tc.infer(&t), Span::default())?;
        self.open_binders(t, fty, &mask)
    }

    fn class_of(&self, ty: &T) -> Option<String> {
        let (h, _) = app_spine(&self.tc.zonk(ty));
        match &*h {
            Term::Const(n, _) if self.tables.traits.contains_key(&**n) => Some(n.to_string()),
            _ => None,
        }
    }

    /// Find an instance for the class application `goal`: first the bounds in
    /// scope, then declared impls (whose own bounds become subgoals).
    fn synth(&mut self, goal: &T, depth: usize, span: Span) -> R<Option<T>> {
        if depth > 12 {
            return Ok(None);
        }
        let g = self.tc.zonk(goal);
        let Some(class) = self.class_of(&g) else {
            return Ok(None);
        };
        // the impl being built: a dictionary of the methods built so far
        if let Some(p) = &self.pending {
            if p.trait_name == class {
                let class_app = mk_apps(&cnst(class.as_str().into(), vec![]), &p.class_args);
                let fields: Vec<T> = p
                    .built
                    .iter()
                    .zip(&p.holes)
                    .map(|(b, &h)| b.clone().unwrap_or_else(|| fvar(h)))
                    .collect();
                let mut args = p.class_args.clone();
                args.extend(fields);
                let dict = mk_apps(&cnst(format!("{class}.mk").as_str().into(), vec![]), &args);
                let snap = self.tc.snapshot();
                if from_kernel(self.tc.is_def_eq(&class_app, &g), span)? {
                    return Ok(Some(dict));
                }
                self.tc.restore(snap);
            }
        }
        for li in self.local_insts.clone() {
            let lty = from_kernel(self.tc.infer(&li), span)?;
            let snap = self.tc.snapshot();
            if from_kernel(self.tc.is_def_eq(&lty, &g), span)? {
                return Ok(Some(li));
            }
            self.tc.restore(snap);
        }
        let names = self.tables.insts.get(&class).cloned().unwrap_or_default();
        for name in names {
            let snap = self.tc.snapshot();
            let (term, res, subgoals) = self.open_instance(&name)?;
            if !from_kernel(self.tc.is_def_eq(&res, &g), span)? {
                self.tc.restore(snap);
                continue;
            }
            let mut ok = true;
            for sg in subgoals {
                let dom = from_kernel(self.tc.infer(&sg), span)?;
                match self.synth(&dom, depth + 1, span)? {
                    Some(t) if from_kernel(self.tc.is_def_eq(&sg, &t), span)? => {}
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                return Ok(Some(term));
            }
            self.tc.restore(snap);
        }
        Ok(None)
    }

    /// Does a class goal still have unknowns in the parameters that select the
    /// implementation? (Output parameters may be unknown: the implementation fixes them.)
    fn stuck_outside_outs(&self, goal: &T) -> bool {
        if first_mvar(goal).is_none() {
            return false;
        }
        let (h, args) = app_spine(goal);
        let Term::Const(n, _) = &*h else {
            return true;
        };
        let Some(info) = self.tables.traits.get(&**n) else {
            return true;
        };
        args.iter()
            .enumerate()
            .any(|(i, a)| !info.outs.get(i).copied().unwrap_or(false) && first_mvar(a).is_some())
    }

    /// Resolve pending instance arguments. A goal whose type still has
    /// metavariables is postponed unless `force` is set.
    fn solve_goals(&mut self, force: bool) -> R<()> {
        self.solve_goals_core(force)?;
        self.run_pending_by(force)
    }

    /// Run the `by` blocks whose goals are fully known (all of them when `force`).
    fn run_pending_by(&mut self, force: bool) -> R<()> {
        loop {
            let pending = std::mem::take(&mut self.pending_by);
            if pending.is_empty() {
                return Ok(());
            }
            let mut rest = Vec::new();
            let mut progress = false;
            for p in pending {
                let ty = from_kernel(self.tc.infer(&p.mv), p.span)?;
                let ty = self.tc.zonk(&ty);
                if first_mvar(&ty).is_some() || has_level_mvar(&ty) {
                    rest.push(p);
                    continue;
                }
                let saved = std::mem::replace(&mut self.scope, p.scope.clone());
                let pf = self.prove(&ty, &p.tactics, p.span);
                self.scope = saved;
                let pf = pf?;
                from_kernel(self.tc.is_def_eq(&p.mv, &pf), p.span)?;
                progress = true;
            }
            let done = rest.is_empty();
            self.pending_by = rest;
            if done {
                return Ok(());
            }
            if !progress {
                if force {
                    return err(
                        self.pending_by[0].span,
                        "cannot tell what this `by` block should prove; add a type annotation",
                    );
                }
                return Ok(());
            }
        }
    }

    fn solve_goals_core(&mut self, force: bool) -> R<()> {
        loop {
            let goals = std::mem::take(&mut self.goals);
            if goals.is_empty() {
                return Ok(());
            }
            let mut rest = Vec::new();
            let mut progress = false;
            for (mv, span) in goals {
                if !matches!(&*self.tc.zonk(&mv), Term::MVar(_)) {
                    continue; // already solved by unification
                }
                let ty = from_kernel(self.tc.infer(&mv), span)?;
                let ty = self.tc.zonk(&ty);
                let stuck = self.stuck_outside_outs(&ty);
                // Like Rust, never pick an impl to *determine* a type: a goal whose
                // type is still unknown stays pending, and is an error at the end.
                if stuck {
                    rest.push((mv, span));
                    continue;
                }
                match self.synth(&ty, 0, span)? {
                    Some(t) => {
                        from_kernel(self.tc.is_def_eq(&mv, &t), span)?;
                        progress = true;
                    }
                    None if stuck => rest.push((mv, span)),
                    None => {
                        return err(
                            span,
                            format!("no implementation of `{}` was found", self.pp(&ty)),
                        )
                    }
                }
            }
            let done = rest.is_empty();
            self.goals = rest;
            if done || !progress {
                if force && !self.goals.is_empty() {
                    let (mv, span) = self.goals[0].clone();
                    let ty = from_kernel(self.tc.infer(&mv), span)?;
                    return err(
                        span,
                        format!(
                            "cannot tell which implementation of `{}` to use; add a type annotation",
                            self.pp(&ty)
                        ),
                    );
                }
                return Ok(());
            }
        }
    }

    fn method_args<'e>(b: &T, base: &'e Expr, args: &'e [Expr]) -> Vec<Arg<'e>> {
        std::iter::once(Arg::Recv(b.clone(), base))
            .chain(args.iter().map(Arg::Expr))
            .collect()
    }

    /// `base.m(args)`: an inherent method or projection `Ty.m`, or a trait method.
    fn elab_method_call(
        &mut self,
        base: &Expr,
        m: &Ident,
        args: &[Expr],
        exp: Option<&T>,
        span: Span,
    ) -> R<T> {
        let b = self.elab(base, None)?;
        let b = self.tc.zonk(&b);
        let bt = from_kernel(self.tc.infer(&b), base.span)?;
        let bt = self.tc.zonk(&bt);
        let bt = from_kernel(self.tc.whnf(&bt), base.span)?;
        // `T.method(args)` with `T` a type: a trait method with `Self := T`
        if matches!(&*bt, Term::Sort(_)) {
            let traits = self
                .tables
                .methods
                .get(&m.name)
                .cloned()
                .unwrap_or_default();
            let Some(tn) = traits.first() else {
                return err(m.span, format!("no method `{}` found", m.name));
            };
            let (head, mask) = self.const_term(&format!("{tn}.{}", m.name));
            let mask = mask.get(1..).map(<[Bk]>::to_vec).unwrap_or_default();
            let call_args: Vec<Arg> = args.iter().map(Arg::Expr).collect();
            return self.elab_app((app(head, b), mask), call_args, exp, span);
        }
        let (h, _) = app_spine(&bt);
        if let Term::Const(tn, _) = &*h {
            let inherent = format!("{tn}.{}", m.name);
            if matches!(self.env.get(&inherent), Some(Decl::Def { .. })) {
                let head = self.const_term(&inherent);
                return self.elab_app(head, Self::method_args(&b, base, args), exp, span);
            }
        }
        let traits = self
            .tables
            .methods
            .get(&m.name)
            .cloned()
            .unwrap_or_default();
        if traits.is_empty() {
            return err(
                m.span,
                format!("no method `{}` found for type `{}`", m.name, self.pp(&bt)),
            );
        }
        let mut first_err = None;
        for tn in &traits {
            let head = self.const_term(&format!("{tn}.{}", m.name));
            if traits.len() == 1 {
                return self.elab_app(head, Self::method_args(&b, base, args), exp, span);
            }
            let (snap, ngoals) = (self.tc.snapshot(), self.goals.len());
            match self.elab_app(head, Self::method_args(&b, base, args), exp, span) {
                Ok(t) => return Ok(t),
                Err(e) => {
                    self.tc.restore(snap);
                    self.goals.truncate(ngoals);
                    first_err.get_or_insert(e);
                }
            }
        }
        Err(first_err.expect("at least one candidate trait"))
    }

    /// Replace `Trait.method Ty inst` by the method's body when `inst` is a
    /// closed instance, so statically known calls do not pay for the dictionary.
    fn devirt(&mut self, t: &T) -> T {
        match &**t {
            Term::App(..) => {
                let (f, args) = app_spine(t);
                let args: Vec<T> = args.iter().map(|a| self.devirt(a)).collect();
                if let Term::Const(n, _) = &*f {
                    if let Some((tn, mn)) = n.split_once('.') {
                        let nparams =
                            self.tables.traits.get(tn).and_then(|i| {
                                i.methods.iter().any(|m| m == mn).then_some(i.nparams)
                            });
                        if let Some(np) = nparams {
                            let mk = format!("{tn}.mk");
                            let is_mk = args.len() > np
                                && matches!(&*app_spine(&args[np]).0, Term::Const(c, _) if **c == *mk);
                            if args.len() > np
                                && args[..=np].iter().all(|a| !has_bvar(a))
                                && (is_mk || !has_fvar(&args[np]))
                                && first_mvar(&args[np]).is_none()
                            {
                                let head = mk_apps(&f, &args[..=np]);
                                if let Ok(r) = self.tc.whnf(&head) {
                                    if r != head {
                                        let again = head_beta(&mk_apps(&r, &args[np + 1..]));
                                        return self.devirt(&again);
                                    }
                                }
                            }
                        }
                    }
                }
                mk_apps(&self.devirt(&f), &args)
            }
            Term::Lam(m, ty, b) => lam(*m, self.devirt(ty), self.devirt(b)),
            Term::Pi(m, ty, b) => pi(*m, self.devirt(ty), self.devirt(b)),
            Term::Let(m, ty, v, b) => let_(*m, self.devirt(ty), self.devirt(v), self.devirt(b)),
            _ => t.clone(),
        }
    }

    /// Elaborate a block. Bindings and effects go to `self.lets`; unless `hoist`
    /// is set they are wrapped around the result here (a hoisted block leaves
    /// them for the enclosing binder, so that assignments to outer variables
    /// stay in scope after the block).
    fn elab_block_opts(&mut self, b: &Block, exp: Option<&T>, hoist: bool) -> R<T> {
        let depth = self.scope.len();
        let mark = self.lets.len();
        for s in &b.stmts {
            match s {
                Stmt::Let {
                    mutable,
                    name,
                    ty,
                    init,
                } => {
                    let (val, vty) = match ty {
                        Some(t) => {
                            let t = self.elab_type(t)?;
                            (self.elab_check(init, &t)?, t)
                        }
                        None => {
                            let v = self.elab(init, None)?;
                            let t = from_kernel(self.tc.infer(&v), init.span)?;
                            (v, t)
                        }
                    };
                    let vty = self.tc.zonk(&vty);
                    let x = self.tc.fresh(&name.name, vty.clone(), Mult::Omega);
                    self.lets.push((x, vty, val));
                    let key = if *mutable {
                        mut_key(&name.name)
                    } else {
                        name.name.clone()
                    };
                    self.scope.push((key, fvar(x)));
                }
                Stmt::Bind { name, .. } => {
                    return err(name.span, "`<-` is only allowed inside a `do` block");
                }
                Stmt::Assign { target, op, value } => {
                    self.elab_assign(target, *op, value, target.span)?;
                }
                Stmt::Expr(e) => {
                    let v = self.elab(e, None)?;
                    let t = from_kernel(self.tc.infer(&v), e.span)?;
                    let t = self.tc.zonk(&t);
                    let x = self.tc.fresh("_", t.clone(), Mult::Omega);
                    self.lets.push((x, t, v));
                }
            }
        }
        let body = match &b.tail {
            Some(t) => self.elab(t, exp)?,
            None => {
                if let Some(exp) = exp {
                    self.coerce(self.unit_value(), exp, b.span)?;
                }
                self.unit_value()
            }
        };
        self.scope.truncate(depth);
        if hoist {
            Ok(body)
        } else {
            Ok(self.wrap_lets(mark, body))
        }
    }

    // ---- mutation as rebinding ----

    fn lookup_scope(&self, name: &str) -> Option<usize> {
        self.scope.iter().rposition(|(n, _)| plain_name(n) == name)
    }

    /// Wrap the bindings accumulated since `mark` around `t`.
    fn wrap_lets(&mut self, mark: usize, t: T) -> T {
        let mine = self.lets.split_off(mark);
        let mut r = self.tc.zonk(&t);
        for (x, ty, val) in mine.into_iter().rev() {
            let (ty, val) = (self.tc.zonk(&ty), self.tc.zonk(&val));
            r = let_(Mult::Omega, ty, val, abstract_fvars(&r, &[x]));
        }
        r
    }

    /// Run `f` and wrap the bindings it produced around its result.
    fn scoped(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let mark = self.lets.len();
        let v = f(self)?;
        Ok(self.wrap_lets(mark, v))
    }

    /// The mutable variables in scope (the latest binding of each name).
    fn state_vars(&self) -> Vec<(String, usize)> {
        let mut out = Vec::new();
        for (i, (n, _)) in self.scope.iter().enumerate() {
            if n.starts_with(MUT) && self.lookup_scope(plain_name(n)) == Some(i) {
                out.push((plain_name(n).to_string(), i));
            }
        }
        out
    }

    fn state_terms(&self, vars: &[(String, usize)]) -> Vec<T> {
        vars.iter().map(|(_, i)| self.scope[*i].1.clone()).collect()
    }

    fn state_types(&mut self, vars: &[(String, usize)]) -> R<Vec<T>> {
        let mut tys = Vec::new();
        for t in self.state_terms(vars) {
            let ty = from_kernel(self.tc.infer(&t), Span::default())?;
            tys.push(self.tc.zonk(&ty));
        }
        Ok(tys)
    }

    fn restore_state(&mut self, vars: &[(String, usize)], terms: &[T]) {
        for ((_, i), t) in vars.iter().zip(terms) {
            self.scope[*i].1 = t.clone();
        }
    }

    /// `(v, state)`: a branch's value together with the mutable variables as it leaves them.
    fn state_pair(&mut self, st: &StateCtx, v: T) -> T {
        let cur = self.state_terms(&st.vars);
        prod_mk(&st.r, &tuple_ty(&st.tys), v, tuple_mk(&st.tys, &cur))
    }

    /// After a construct that returned `(value, state)`: bind it, rebind every
    /// mutable variable to its component, and give back the value.
    fn rebind_state(&mut self, st: &StateCtx, pair_ty: &T, pair: T) -> T {
        let p = self.tc.fresh("branch", pair_ty.clone(), Mult::Omega);
        self.lets.push((p, pair_ty.clone(), pair));
        let s_ty = tuple_ty(&st.tys);
        let snd = prod_snd(&st.r, &s_ty, fvar(p));
        for (i, (name, idx)) in st.vars.iter().enumerate() {
            let x2 = self.tc.fresh(name, st.tys[i].clone(), Mult::Omega);
            self.lets
                .push((x2, st.tys[i].clone(), tuple_get(&st.tys, snd.clone(), i)));
            self.scope[*idx].1 = fvar(x2);
        }
        prod_fst(&st.r, &s_ty, fvar(p))
    }

    /// Make the mutable variables read-only: closures and loop bodies capture them by value.
    fn freeze_mutables(&mut self) -> Vec<(usize, String)> {
        let mut saved = Vec::new();
        for (i, (n, _)) in self.scope.iter_mut().enumerate() {
            if n.starts_with(MUT) {
                saved.push((i, n.clone()));
                *n = plain_name(n).to_string();
            }
        }
        saved
    }

    fn unfreeze_mutables(&mut self, saved: Vec<(usize, String)>) {
        for (i, n) in saved {
            if i < self.scope.len() {
                self.scope[i].0 = n;
            }
        }
    }

    fn resolve_place(&mut self, e: &Expr, purpose: &str) -> R<Place> {
        match &e.kind {
            ExprKind::Var(n) => {
                let Some(idx) = self.lookup_scope(n) else {
                    return err(e.span, format!("unknown identifier `{n}`"));
                };
                if !self.scope[idx].0.starts_with(MUT) {
                    let behind_shared = matches!(&*self.scope[idx].1, Term::FVar(id) if self.shared_refs.contains(id));
                    let (code, msg) = if behind_shared {
                        (
                            "E0594",
                            format!("cannot {purpose} `{n}`: it is behind a `&` reference (use `&mut` to allow changes)"),
                        )
                    } else if purpose == "assign to" {
                        (
                            "E0384",
                            format!("cannot assign to `{n}`, which is not declared `mut` (write `let mut {n} := ..`; closures and loop bodies capture variables by value)"),
                        )
                    } else {
                        (
                            "E0596",
                            format!("cannot {purpose} `{n}`, which is not declared `mut` (write `let mut {n} := ..`)"),
                        )
                    };
                    let mut e = ElabError::new(e.span, msg);
                    e.code = Some(code.to_string());
                    return Err(e);
                }
                Ok(Place {
                    name: n.clone(),
                    idx,
                    path: vec![],
                })
            }
            ExprKind::Field(b, f) => {
                let mut p = self.resolve_place(b, purpose)?;
                p.path.push(f.name.clone());
                Ok(p)
            }
            ExprKind::Deref(b) => self.resolve_place(b, purpose),
            _ => err(e.span, "this expression is not a place"),
        }
    }

    /// The struct behind `cur`: its metadata, type arguments and name.
    fn struct_of(&mut self, cur: &T, field: &str, span: Span) -> R<(StructMeta, Vec<T>, String)> {
        let ty = from_kernel(self.tc.infer(cur), span)?;
        let ty = self.tc.zonk(&ty);
        let ty = from_kernel(self.tc.whnf(&ty), span)?;
        let (h, args) = app_spine(&ty);
        let Term::Const(n, _) = &*h else {
            return err(span, format!("`{}` has no field `{field}`", self.pp(&ty)));
        };
        let Some(meta) = self.tables.structs.get(&**n).cloned() else {
            return err(
                span,
                format!("`{n}` is not a struct, so it has no field `{field}`"),
            );
        };
        if !meta.fields.iter().any(|f| f == field) {
            return err(span, format!("struct `{n}` has no field `{field}`"));
        }
        let params = args[..meta.nparams].to_vec();
        Ok((meta, params, n.to_string()))
    }

    fn project(&mut self, cur: &T, field: &str, span: Span) -> R<T> {
        let (_, params, sname) = self.struct_of(cur, field, span)?;
        let mut args = params;
        args.push(cur.clone());
        Ok(mk_apps(
            &cnst(format!("{sname}.{field}").as_str().into(), vec![]),
            &args,
        ))
    }

    /// `cur` with the field path replaced by `newval` (nested struct update).
    fn update_path(&mut self, cur: &T, path: &[String], newval: &T, span: Span) -> R<T> {
        let Some((f, rest)) = path.split_first() else {
            return Ok(newval.clone());
        };
        let (meta, params, _) = self.struct_of(cur, f, span)?;
        let inner_cur = self.project(cur, f, span)?;
        let inner_new = self.update_path(&inner_cur, rest, newval, span)?;
        let mut args = params;
        for k in &meta.fields {
            args.push(if k == f {
                inner_new.clone()
            } else {
                self.project(cur, k, span)?
            });
        }
        Ok(mk_apps(&cnst(meta.ctor.as_str().into(), vec![]), &args))
    }

    fn read_place(&mut self, p: &Place, span: Span) -> R<(T, T)> {
        let mut cur = self.scope[p.idx].1.clone();
        for f in &p.path {
            cur = self.project(&cur, f, span)?;
        }
        let ty = from_kernel(self.tc.infer(&cur), span)?;
        Ok((cur, self.tc.zonk(&ty)))
    }

    /// `place := newval`: a fresh binding that the variable then refers to.
    fn assign_place(&mut self, p: &Place, newval: T, span: Span) -> R<()> {
        let cur_root = self.scope[p.idx].1.clone();
        let root_ty = from_kernel(self.tc.infer(&cur_root), span)?;
        let root_ty = self.tc.zonk(&root_ty);
        let new_root = self.update_path(&cur_root, &p.path, &newval, span)?;
        let nt = from_kernel(self.tc.infer(&new_root), span)?;
        self.coerce_eq(&nt, &root_ty, span)?;
        let x2 = self.tc.fresh(&p.name, root_ty.clone(), Mult::Omega);
        self.lets.push((x2, root_ty, new_root));
        self.scope[p.idx].1 = fvar(x2);
        Ok(())
    }

    /// `x = e`, `x.f = e`, `*p = e`, and `x op= e`.
    fn elab_assign(&mut self, target: &Expr, op: Option<BinOp>, value: &Expr, span: Span) -> R<()> {
        let place = self.resolve_place(target, "assign to")?;
        let (_, ty) = self.read_place(&place, span)?;
        let rhs = match op {
            Some(o) => Expr {
                kind: ExprKind::Binary(o, Box::new(target.clone()), Box::new(value.clone())),
                span,
            },
            None => value.clone(),
        };
        let v = self.elab_check(&rhs, &ty)?;
        self.assign_place(&place, v, span)
    }

    // ---- do notation ----

    fn io_type(&self, a: &T) -> T {
        app(cnst("IO".into(), vec![]), a.clone())
    }

    fn elab_do(&mut self, b: &Block, exp: Option<&T>, span: Span) -> R<T> {
        let r = match exp {
            Some(t) => {
                let w = from_kernel(self.tc.whnf(t), span)?;
                match &*w {
                    Term::App(f, a) if matches!(&**f, Term::Const(n, _) if &**n == "IO") => {
                        a.clone()
                    }
                    Term::MVar(_) => {
                        let l = self.tc.new_level_mvar();
                        let sort_mv = self.new_mvar(sort(l), span);
                        let r = self.new_mvar(sort_mv, span);
                        self.coerce_eq(&w, &self.io_type(&r), span)?;
                        r
                    }
                    _ => {
                        return err(
                            span,
                            format!(
                                "a `do` block has type `IO _`, but `{}` is expected here",
                                self.pp(t)
                            ),
                        )
                    }
                }
            }
            None => {
                let l = self.tc.new_level_mvar();
                let sort_mv = self.new_mvar(sort(l), span);
                self.new_mvar(sort_mv, span)
            }
        };
        self.do_stmts(&b.stmts, b.tail.as_deref(), &r, span)
    }

    fn coerce_eq(&mut self, a: &T, b: &T, span: Span) -> R<()> {
        if from_kernel(self.tc.is_def_eq(a, b), span)? {
            Ok(())
        } else {
            err(
                span,
                format!("type mismatch: `{}` vs `{}`", self.pp(a), self.pp(b)),
            )
        }
    }

    fn do_stmts(&mut self, stmts: &[Stmt], tail: Option<&Expr>, r: &T, span: Span) -> R<T> {
        let bind = |a: &T, act: T, k: T| -> T {
            mk_apps(
                &cnst("IO.bind".into(), vec![]),
                &[a.clone(), r.clone(), act, k],
            )
        };
        let mark = self.lets.len();
        let result = match stmts.split_first() {
            None => match tail {
                Some(t) => {
                    let io = self.io_type(r);
                    self.elab_action(t, &io)?
                }
                None => {
                    let unit = self.unit_type();
                    self.coerce_eq(r, &unit, span)?;
                    mk_apps(&cnst("IO.pure".into(), vec![]), &[unit, self.unit_value()])
                }
            },
            Some((Stmt::Bind { name, ty, action }, rest)) => {
                let a = match ty {
                    Some(t) => self.elab_type(t)?,
                    None => self.fresh_type(action.span),
                };
                let io = self.io_type(&a);
                let act = self.elab_action(action, &io)?;
                let a = self.tc.zonk(&a);
                let x = self.tc.fresh(&name.name, a.clone(), Mult::Omega);
                self.scope.push((name.name.clone(), fvar(x)));
                let body = self.do_stmts(rest, tail, r, span);
                self.scope.pop();
                let lam = self.close_lam(x, &body?);
                bind(&a, act, lam)
            }
            Some((Stmt::Expr(e), rest))
                if matches!(
                    e.kind,
                    ExprKind::If(..) | ExprKind::Match(..) | ExprKind::Block(_)
                ) && !self.state_vars().is_empty() =>
            {
                // `if c { A } else { B }; rest` with mutable variables `w..` in scope:
                //   let s <- if c { A; pure((w..)) } else { B; pure((w..)) };  w.. = s..;  rest
                let names: Vec<String> = self.state_vars().into_iter().map(|(n, _)| n).collect();
                self.synth_counter += 1;
                let sname = format!("__state{}", self.synth_counter);
                let sp = e.span;
                let var = |n: &str| Expr {
                    kind: ExprKind::Var(n.into()),
                    span: sp,
                };
                let mut new = vec![Stmt::Bind {
                    name: Ident {
                        name: sname.clone(),
                        span: sp,
                    },
                    ty: None,
                    action: add_state_tail(e, &names),
                }];
                for (i, n) in names.iter().enumerate() {
                    new.push(Stmt::Assign {
                        target: var(n),
                        op: None,
                        value: state_proj_expr(var(&sname), i, names.len()),
                    });
                }
                new.extend(rest.iter().cloned());
                return self.do_stmts(&new, tail, r, span);
            }
            Some((Stmt::Expr(e), rest)) => {
                let control = matches!(
                    e.kind,
                    ExprKind::If(..) | ExprKind::Match(..) | ExprKind::Block(_)
                );
                if control {
                    let a = self.fresh_type(e.span);
                    let io = self.io_type(&a);
                    let act = self.elab_action(e, &io)?;
                    let a = self.tc.zonk(&a);
                    let x = self.tc.fresh("_", a.clone(), Mult::Omega);
                    let body = self.do_stmts(rest, tail, r, span)?;
                    let lam = self.close_lam(x, &body);
                    bind(&a, act, lam)
                } else {
                    // an `IO` action, or a plain statement such as `inc(&mut x);`
                    let act = self.elab(e, None)?;
                    let ty = from_kernel(self.tc.infer(&act), e.span)?;
                    let ty = self.tc.zonk(&ty);
                    let ty = from_kernel(self.tc.whnf(&ty), e.span)?;
                    match &*ty {
                        Term::App(f, a) if matches!(&**f, Term::Const(n, _) if &**n == "IO") => {
                            let a = a.clone();
                            let x = self.tc.fresh("_", a.clone(), Mult::Omega);
                            let body = self.do_stmts(rest, tail, r, span)?;
                            let lam = self.close_lam(x, &body);
                            bind(&a, act, lam)
                        }
                        _ => self.do_stmts(rest, tail, r, span)?,
                    }
                }
            }
            Some((Stmt::Assign { target, op, value }, rest)) => {
                self.elab_assign(target, *op, value, target.span)?;
                self.do_stmts(rest, tail, r, span)?
            }
            Some((
                Stmt::Let {
                    mutable,
                    name,
                    ty,
                    init,
                },
                rest,
            )) => {
                let (val, vty) = match ty {
                    Some(t) => {
                        let t = self.elab_type(t)?;
                        (self.elab_check(init, &t)?, t)
                    }
                    None => {
                        let v = self.elab(init, None)?;
                        let t = from_kernel(self.tc.infer(&v), init.span)?;
                        (v, t)
                    }
                };
                let vty = self.tc.zonk(&vty);
                let x = self.tc.fresh(&name.name, vty.clone(), Mult::Omega);
                let key = if *mutable {
                    mut_key(&name.name)
                } else {
                    name.name.clone()
                };
                self.scope.push((key, fvar(x)));
                let body = self.do_stmts(rest, tail, r, span);
                self.scope.pop();
                let body = self.tc.zonk(&body?);
                let val = self.tc.zonk(&val);
                let_(Mult::Omega, vty, val, abstract_fvars(&body, &[x]))
            }
        };
        // effects of this statement scope over the statements after it
        Ok(self.wrap_lets(mark, result))
    }

    /// A statement of a `do` block: blocks, `if` and `match` branch into `do` blocks.
    fn elab_action(&mut self, e: &Expr, io: &T) -> R<T> {
        match &e.kind {
            ExprKind::Block(b) => {
                let t = self.elab_do(b, Some(io), e.span)?;
                self.coerce(t, io, e.span)
            }
            ExprKind::If(..) | ExprKind::Match(..) => {
                self.do_mode = true;
                let r = self.elab(e, Some(io));
                self.do_mode = false;
                let t = r?;
                self.coerce(t, io, e.span)
            }
            _ => self.elab_check(e, io),
        }
    }

    /// `|x, y| body`: parameter types come from the expected function type
    /// unless annotated.
    fn elab_lambda(
        &mut self,
        params: &[LamParam],
        body: &Expr,
        exp: Option<&T>,
        span: Span,
    ) -> R<T> {
        let (depth, nlocal) = (self.scope.len(), self.local_insts.len());
        let frozen = self.freeze_mutables();
        let mut xs = Vec::new();
        let mut expected = exp.cloned();
        for p in params {
            let from_exp = match &expected {
                Some(t) => {
                    let t = self.tc.zonk(t);
                    let w = from_kernel(self.tc.whnf(&t), p.name.span)?;
                    match &*w {
                        Term::Pi(m, d, b) => Some((*m, d.clone(), b.clone())),
                        _ => None,
                    }
                }
                None => None,
            };
            let ty = match (&p.ty, &from_exp) {
                (Some(t), _) => self.elab_type(t)?,
                (None, Some((_, d, _))) => d.clone(),
                (None, None) => {
                    return err(
                        p.name.span,
                        "cannot infer the type of this closure parameter; add an annotation like `|x: Nat|`",
                    )
                }
            };
            let mult = from_exp.as_ref().map_or(Mult::Omega, |(m, _, _)| *m);
            if let Some((_, d, _)) = &from_exp {
                self.coerce_eq(&ty, d, p.name.span)?;
            }
            let x = self.tc.fresh(&p.name.name, ty, mult);
            self.scope.push((p.name.name.clone(), fvar(x)));
            xs.push(x);
            expected = from_exp.map(|(_, _, b)| instantiate(&b, &fvar(x)));
        }
        let b = self.scoped(|cx| match &expected {
            Some(t) => cx.elab_check(body, t),
            None => cx.elab(body, None),
        });
        self.scope.truncate(depth);
        self.local_insts.truncate(nlocal);
        self.unfreeze_mutables(frozen);
        let b = b?;
        let _ = span;
        self.tc.zonk_locals();
        let b = self.tc.zonk(&b);
        Ok(self.tc.mk_lam(&xs, &b))
    }

    /// `for x in xs { body }` is `for_each(xs, fun x => do { body })`.
    fn elab_for(&mut self, var: &Ident, iter: &Expr, body: &Block, span: Span) -> R<T> {
        let it = self.elab(iter, None)?;
        let it = self.tc.zonk(&it);
        let ity = from_kernel(self.tc.infer(&it), iter.span)?;
        let ity = self.tc.zonk(&ity);
        let ity = from_kernel(self.tc.whnf(&ity), iter.span)?;
        let elem = match &*ity {
            Term::App(f, a) if matches!(&**f, Term::Const(n, _) if &**n == "List") => a.clone(),
            _ => {
                return err(
                    iter.span,
                    format!(
                        "`for` loops iterate over a `List`, but this has type `{}`",
                        self.pp(&ity)
                    ),
                )
            }
        };
        let x = self.tc.fresh(&var.name, elem.clone(), Mult::Omega);
        let frozen = self.freeze_mutables();
        self.scope.push((var.name.clone(), fvar(x)));
        let unit_io = self.io_type(&self.unit_type());
        let b = self.elab_do(body, Some(&unit_io), span);
        self.scope.pop();
        self.unfreeze_mutables(frozen);
        let lam = self.close_lam(x, &b?);
        Ok(mk_apps(&cnst("for_each".into(), vec![]), &[elem, it, lam]))
    }

    fn fresh_type(&mut self, span: Span) -> T {
        let l = self.tc.new_level_mvar();
        let s = self.new_mvar(sort(l), span);
        self.new_mvar(s, span)
    }

    /// `fun x => body` with `x` a local variable.
    fn close_lam(&mut self, x: u32, body: &T) -> T {
        self.tc.zonk_locals();
        let body = self.tc.zonk(body);
        self.tc.mk_lam(&[x], &body)
    }

    // ---- pattern matching ----

    fn global_ctor(&self, name: &str) -> Option<String> {
        for cand in self.name_candidates(name) {
            let full = self.aliases.get(&cand).cloned().unwrap_or(cand);
            if matches!(self.env.get(&full), Some(Decl::Ctor(_))) {
                return Some(full);
            }
        }
        None
    }

    fn elab_pattern(&self, e: &Expr) -> R<Pat> {
        match &e.kind {
            ExprKind::Wild => Ok(Pat::Wild),
            ExprKind::Var(n) => Ok(match self.global_ctor(n) {
                Some(full) => Pat::Ctor(full, vec![]),
                None => Pat::Var(n.clone()),
            }),
            ExprKind::Field(..) => match path_name(e).and_then(|p| self.global_ctor(&p)) {
                Some(full) => Ok(Pat::Ctor(full, vec![])),
                None => err(e.span, "unknown constructor in pattern"),
            },
            ExprKind::Nat(0) => Ok(Pat::Ctor("Nat.zero".into(), vec![])),
            ExprKind::Nat(k) => {
                let inner = self.elab_pattern(&Expr {
                    kind: ExprKind::Nat(k - 1),
                    span: e.span,
                })?;
                Ok(Pat::Ctor("Nat.succ".into(), vec![inner]))
            }
            ExprKind::Call(f, args) => {
                let Some(full) = path_name(f).and_then(|p| self.global_ctor(&p)) else {
                    return err(f.span, "unknown constructor in pattern");
                };
                let subs = args
                    .iter()
                    .map(|a| self.elab_pattern(a))
                    .collect::<R<Vec<_>>>()?;
                Ok(Pat::Ctor(full, subs))
            }
            _ => err(e.span, "this kind of pattern is not supported yet"),
        }
    }

    fn elab_match(&mut self, scrut: &Expr, arms: &[Arm], exp: Option<&T>, span: Span) -> R<T> {
        let do_mode = std::mem::take(&mut self.do_mode);
        let ret = match exp {
            Some(t) => t.clone(),
            None => {
                let l = self.tc.new_level_mvar();
                let s = self.new_mvar(sort(l), span);
                self.new_mvar(s, span)
            }
        };
        let s = self.elab(scrut, None)?;
        let s = self.tc.zonk(&s);
        let (x, wrap) = match &*s {
            Term::FVar(id) => (*id, None),
            _ => {
                let ty = from_kernel(self.tc.infer(&s), scrut.span)?;
                let ty = self.tc.zonk(&ty);
                (
                    self.tc.fresh("m", ty.clone(), Mult::Omega),
                    Some((ty, s.clone())),
                )
            }
        };
        if self.is_indexed(x) {
            let r = self.elab_indexed_match(x, arms, &ret, span)?;
            return Ok(match wrap {
                None => r,
                Some((ty, val)) => {
                    let r = self.tc.zonk(&r);
                    let_(Mult::Omega, ty, val, abstract_fvars(&r, &[x]))
                }
            });
        }
        let mut rows = Vec::new();
        for a in arms {
            rows.push(Row {
                pats: vec![self.elab_pattern(&a.pat)?],
                binds: vec![],
                body: &a.body,
            });
        }
        let top = match &mut self.rec {
            Some(rc) if rc.decr == x && !rc.in_top => {
                rc.in_top = true;
                true
            }
            _ => false,
        };
        // mutable variables in scope are threaded through the arms as a pair
        // (not in a `do` statement: `do_stmts` threads them through the action instead)
        let vars = if do_mode {
            Vec::new()
        } else {
            self.state_vars()
        };
        let st = if vars.is_empty() {
            None
        } else {
            let tys = self.state_types(&vars)?;
            Some(StateCtx {
                r: ret.clone(),
                vars: vars.clone(),
                tys,
            })
        };
        let target_ty = match &st {
            Some(st) => prod_ty(&ret, &tuple_ty(&st.tys)),
            None => ret.clone(),
        };
        let saved_state = self.stateful.take();
        let saved_leaf_do = std::mem::replace(&mut self.leaf_do, do_mode);
        self.stateful = st.clone();
        let r = self.compile_match(vec![x], rows, &target_ty, top, span);
        self.stateful = saved_state;
        self.leaf_do = saved_leaf_do;
        if top {
            if let Some(rc) = &mut self.rec {
                rc.in_top = false;
            }
        }
        let r = r?;
        let r = match wrap {
            None => r,
            Some((ty, val)) => {
                let r = self.tc.zonk(&r);
                let_(Mult::Omega, ty, val, abstract_fvars(&r, &[x]))
            }
        };
        Ok(match st {
            Some(st) => self.rebind_state(&st, &target_ty, r),
            None => r,
        })
    }

    /// Decision-tree compilation of a pattern matrix into recursor applications.
    fn compile_match(
        &mut self,
        cols: Vec<u32>,
        rows: Vec<Row<'_>>,
        ret: &T,
        top: bool,
        span: Span,
    ) -> R<T> {
        let Some(first) = rows.first() else {
            return err(span, "non-exhaustive patterns");
        };
        let Some(j) = first.pats.iter().position(|p| matches!(p, Pat::Ctor(..))) else {
            // leaf: bind variables and elaborate the arm
            let depth = self.scope.len();
            for (n, t) in &first.binds {
                self.scope.push((n.clone(), t.clone()));
            }
            for (p, &c) in first.pats.iter().zip(&cols) {
                if let Pat::Var(n) = p {
                    self.scope.push((n.clone(), fvar(c)));
                }
            }
            let leaf_do = self.leaf_do;
            let arm = |cx: &mut Self, ty: &T| -> R<T> {
                if leaf_do {
                    cx.elab_action(first.body, ty)
                } else {
                    cx.elab_check(first.body, ty)
                }
            };
            let r = match self.stateful.take() {
                Some(st) => {
                    let saved = self.state_terms(&st.vars);
                    let res = self.scoped(|cx| {
                        let v = arm(cx, &st.r)?;
                        Ok(cx.state_pair(&st, v))
                    });
                    self.restore_state(&st.vars, &saved);
                    self.stateful = Some(st);
                    res
                }
                None => {
                    // arms must not see each other's assignments
                    let vars = self.state_vars();
                    let saved = self.state_terms(&vars);
                    let res = self.scoped(|cx| arm(cx, ret));
                    self.restore_state(&vars, &saved);
                    res
                }
            };
            self.scope.truncate(depth);
            return r;
        };
        let x = cols[j];
        let xty = from_kernel(self.tc.local_ty(x), span)?;
        let xty = from_kernel(self.tc.whnf(&xty), span)?;
        let (head, targs) = app_spine(&xty);
        let Term::Const(iname, ilevels) = &*head else {
            return err(
                span,
                format!("cannot match on a value of type `{}`", self.pp(&xty)),
            );
        };
        let Some(Decl::Inductive(info)) = self.env.get(iname) else {
            return err(
                span,
                format!("cannot match on a value of type `{}`", self.pp(&xty)),
            );
        };
        if info.nindices > 0 {
            return err(span, "matching on indexed families is not supported yet");
        }
        let info = info.clone();
        let params = targs[..info.nparams].to_vec();
        let iname = iname.to_string();
        let ilevels = ilevels.clone();
        // a function of a `mutual` group on a nested occurrence (`List<Rose>`) is defined by the
        // auxiliary recursor of the family it belongs to: the scrutinee's type is `J args`, the
        // family is the root's
        let in_deep_early = self.rec.as_ref().is_some_and(|rc| rc.deep.is_some());
        let aux_view: Option<AuxView> = if top && !in_deep_early {
            self.rec
                .as_ref()
                .and_then(|rc| rc.mutual.as_ref().and_then(|m| m.view.clone()))
        } else {
            None
        };
        let (root_info, target, fam_params, fam_levels) = match &aux_view {
            Some(v) => {
                let Some(Decl::Inductive(ri)) = self.env.get(&v.root) else {
                    return err(span, "internal error: missing family root");
                };
                (
                    ri.clone(),
                    ri.family.len() + v.nested_idx,
                    v.fam_params.clone(),
                    v.fam_levels.clone(),
                )
            }
            None => {
                let k = info.family.iter().position(|n| **n == *iname).unwrap_or(0);
                (info.clone(), k, params.clone(), ilevels.clone())
            }
        };
        let family: Vec<String> = root_info.family.iter().map(|n| n.to_string()).collect();
        let nested = root_info.nested.clone();
        let ind_nlevels = root_info.lparams.len();
        let (ctors, info_rec): (Vec<String>, Name) = if target < family.len() {
            (
                root_info
                    .family
                    .get(target)
                    .map_or_else(Vec::new, |n| match self.env.get(n) {
                        Some(Decl::Inductive(i)) => i.ctors.iter().map(|c| c.to_string()).collect(),
                        _ => vec![],
                    }),
                match self.env.get(&root_info.family[target]) {
                    Some(Decl::Inductive(i)) => i.rec.clone(),
                    _ => return err(span, "internal error: missing family member"),
                },
            )
        } else {
            let n = &nested[target - family.len()];
            (
                n.ctors.iter().map(|c| c.to_string()).collect(),
                n.rec.clone(),
            )
        };

        // motive: fun (t : I params) => ret[x := t], generalizing the other
        // parameters when this is the top-level split of a recursive function
        let deep_ctx: Option<(Deep, T)> = self.rec.as_ref().and_then(|rc| {
            rc.deep
                .as_ref()
                .and_then(|d| d.below_of.get(&x).map(|bt| (d.clone(), bt.clone())))
        });
        let in_deep = self.rec.as_ref().is_some_and(|rc| rc.deep.is_some());
        let mutual_ms: Option<Vec<T>> = if top && !in_deep {
            self.rec
                .as_ref()
                .and_then(|rc| rc.mutual.as_ref().map(|m| m.motives.clone()))
        } else {
            None
        };
        let others: Vec<u32> = match (&self.rec, top && !in_deep) {
            (Some(rc), true) => rc
                .explicit
                .iter()
                .copied()
                .filter(|&p| p != rc.decr)
                .collect(),
            _ => vec![],
        };
        self.tc.zonk_locals();
        let ret_z = self.tc.zonk(ret);
        // course-of-values mode: the motive also takes the `below` tuple of the scrutinee
        let bq = deep_ctx.as_ref().map(|(d, _)| {
            let ty = self.below_type(d, fvar(x));
            self.tc.fresh("b", ty, Mult::Omega)
        });
        let gen: Vec<u32> = bq.into_iter().chain(others.iter().copied()).collect();
        let motive_res = self.tc.mk_pi(&gen, &ret_z);
        let motive_abs = abstract_fvars(&motive_res, &[x]);
        let ret_abs = abstract_fvars(&ret_z, &[x]);
        let lvl = from_kernel(self.tc.check_is_type(&motive_res), span)?;
        let lvl = self.tc.zonk_level(&lvl);
        let large = match self.env.get(&root_info.rec) {
            Some(Decl::Rec(r)) => r.lparams.len() > ind_nlevels,
            _ => return err(span, "missing recursor"),
        };
        let mut rec_levels = fam_levels.clone();
        if large {
            rec_levels.insert(0, lvl);
        } else if !lvl.is_zero() {
            return err(
                span,
                format!("`{iname}` can only be matched when the result is a proposition"),
            );
        }
        let motive = lam(Mult::Omega, xty.clone(), motive_abs.clone());

        let punit_lvl = if large {
            rec_levels[0].clone()
        } else {
            Level::Zero
        };
        // a mutual family: the other types get the constant `PUnit` motive and
        // `PUnit.unit` minors, only this type's constructors carry real cases
        let mut motives_all: Vec<T> = Vec::new();
        let nested_tys: Vec<T> = nested
            .iter()
            .map(|n| {
                let args: Vec<T> = n
                    .args
                    .iter()
                    .map(|a| instantiate_many(a, &fam_params))
                    .collect();
                mk_apps(&cnst(n.ind.clone(), n.levels.clone()), &args)
            })
            .collect();
        for mi in 0..family.len() + nested.len() {
            if let Some(ms) = &mutual_ms {
                motives_all.push(ms[mi].clone());
            } else if mi == target {
                motives_all.push(motive.clone());
            } else {
                let kt = if mi < family.len() {
                    let fty = from_kernel(self.env.const_type(&family[mi], &fam_levels), span)?;
                    let fty = from_kernel(self.tc.instantiate_pis(&fty, &fam_params), span)?;
                    let (idx, _) = from_kernel(self.tc.telescope(&fty, None), span)?;
                    if !idx.is_empty() {
                        return err(span, "matching on mutual indexed families is not supported");
                    }
                    mk_apps(
                        &cnst(family[mi].as_str().into(), fam_levels.clone()),
                        &fam_params,
                    )
                } else {
                    nested_tys[mi - family.len()].clone()
                };
                motives_all.push(lam(
                    Mult::Omega,
                    kt,
                    cnst("PUnit".into(), vec![punit_lvl.clone()]),
                ));
            }
        }
        let mut rty = from_kernel(self.env.const_type(&info_rec, &rec_levels), span)?;
        for p in fam_params.iter().chain(motives_all.iter()) {
            match &*rty {
                Term::Pi(_, _, b) => rty = instantiate(b, p),
                _ => return err(span, "internal error: malformed recursor type"),
            }
        }

        let mut minors = Vec::new();
        for mi in 0..family.len() + nested.len() {
            if mi != target {
                let nfc: usize = if mi < family.len() {
                    match self.env.get(&family[mi]) {
                        Some(Decl::Inductive(i)) => i.ctors.len(),
                        _ => return err(span, "internal error: missing family member"),
                    }
                } else {
                    nested[mi - family.len()].ctors.len()
                };
                for _ in 0..nfc {
                    let (dom, rest) = match &*rty {
                        Term::Pi(_, d, b) => (d.clone(), b.clone()),
                        _ => return err(span, "internal error: malformed recursor type"),
                    };
                    let m = if mutual_ms.is_some() {
                        // supplied by the function of that type: a stand-in of the right type
                        let fv = self.tc.fresh("foreign", head_beta(&dom), Mult::Omega);
                        fvar(fv)
                    } else {
                        let (bs, _) = from_kernel(self.tc.telescope(&head_beta(&dom), None), span)?;
                        let unit = cnst("PUnit.unit".into(), vec![punit_lvl.clone()]);
                        self.tc.mk_lam(&bs, &unit)
                    };
                    rty = instantiate(&rest, &m);
                    minors.push(m);
                }
                continue;
            }
            for cname in &ctors {
                let cty = from_kernel(self.env.const_type(cname, &ilevels), span)?;
                let rest = from_kernel(self.tc.instantiate_pis(&cty, &params), span)?;
                let (fields, _) = from_kernel(self.tc.telescope(&rest, None), span)?;
                let fterms: Vec<T> = fields.iter().map(|&f| fvar(f)).collect();
                let ctor_app = mk_apps(
                    &cnst(cname.as_str().into(), ilevels.clone()),
                    &[params.clone(), fterms].concat(),
                );
                let ret_c = instantiate(&ret_abs, &ctor_app);

                // induction hypotheses for recursive fields
                let mut ihs = Vec::new();
                for &f in &fields {
                    let fty = from_kernel(self.tc.local_ty(f), span)?;
                    if !family.iter().any(|n| contains_const(&fty, n)) {
                        continue;
                    }
                    let (xs, fbody) = from_kernel(self.tc.telescope(&fty, None), span)?;
                    let (fhead, fargs) = app_spine(&fbody);
                    let fam_idx = match &*fhead {
                        Term::Const(n, _) => family.iter().position(|m| **n == **m).or_else(|| {
                            nested
                                .iter()
                                .zip(&nested_tys)
                                .position(|(nn, nt)| *nn.ind == **n && app_spine(nt).1 == fargs)
                                .map(|k| family.len() + k)
                        }),
                        _ => None,
                    };
                    let own = fam_idx.is_some_and(|k| k < family.len() && family[k] == iname);
                    let applied =
                        mk_apps(&fvar(f), &xs.iter().map(|&v| fvar(v)).collect::<Vec<_>>());
                    let ih_res = match (&mutual_ms, fam_idx) {
                        (Some(ms), Some(k)) => head_beta(&app(
                            ms[k].clone(),
                            mk_apps(&fvar(f), &xs.iter().map(|&v| fvar(v)).collect::<Vec<_>>()),
                        )),
                        _ if own => instantiate(&motive_abs, &applied),
                        _ => cnst("PUnit".into(), vec![punit_lvl.clone()]),
                    };
                    let ih_ty = self.tc.mk_pi(&xs, &ih_res);
                    let ih = self.tc.fresh("ih", ih_ty, Mult::Omega);
                    if top && !in_deep && (own || mutual_ms.is_some()) {
                        if let Some(rc) = &mut self.rec {
                            rc.fields.insert(f, fvar(ih));
                        }
                    }
                    ihs.push(ih);
                }

                // course-of-values: the results for the subterms come out of `below`
                let mut cb = None;
                if let Some((d, _)) = &deep_ctx {
                    let rec_fields: Vec<u32> = {
                        let mut v = Vec::new();
                        for &f in &fields {
                            let fty = from_kernel(self.tc.local_ty(f), span)?;
                            if contains_const(&fty, &iname) {
                                v.push(f);
                            }
                        }
                        v
                    };
                    let b2_ty = self.below_type(d, ctor_app.clone());
                    let b2 = self.tc.fresh("b", b2_ty, Mult::Omega);
                    let comps = self.below_components(b2, rec_fields.len(), span)?;
                    if let Some(rc) = &mut self.rec {
                        for (f, (ih, bt)) in rec_fields.iter().zip(comps) {
                            rc.fields.insert(*f, ih);
                            if let Some(dd) = &mut rc.deep {
                                dd.below_of.insert(*f, bt);
                            }
                        }
                    }
                    cb = Some(b2);
                }

                // specialize the rows to this constructor
                let mut new_cols: Vec<u32> = cols[..j].to_vec();
                new_cols.extend(&fields);
                new_cols.extend(&cols[j + 1..]);
                let mut new_rows = Vec::new();
                for row in &rows {
                    let (before, after) = (&row.pats[..j], &row.pats[j + 1..]);
                    let mut binds = row.binds.clone();
                    let mid: Vec<Pat> = match &row.pats[j] {
                        Pat::Ctor(c, subs) if c == cname => {
                            if subs.len() != fields.len() {
                                return err(
                                    span,
                                    format!(
                                        "constructor `{cname}` takes {} fields, the pattern has {}",
                                        fields.len(),
                                        subs.len()
                                    ),
                                );
                            }
                            subs.clone()
                        }
                        Pat::Ctor(..) => continue,
                        Pat::Var(n) => {
                            binds.push((n.clone(), ctor_app.clone()));
                            vec![Pat::Wild; fields.len()]
                        }
                        Pat::Wild => vec![Pat::Wild; fields.len()],
                    };
                    let pats = [before, &mid[..], after].concat();
                    new_rows.push(Row {
                        pats,
                        binds,
                        body: row.body,
                    });
                }
                if new_rows.is_empty() {
                    return err(span, format!("non-exhaustive patterns: missing `{cname}`"));
                }
                // inside the branch the scrutinee *is* the constructor application
                let xt = fvar(x);
                let saved = self.scope.clone();
                for (_, t) in self.scope.iter_mut() {
                    if *t == xt {
                        *t = ctor_app.clone();
                    }
                }
                if let Some(rc) = &mut self.rec {
                    rc.refined.push((ctor_app.clone(), x));
                }
                let sub = self.compile_match(new_cols, new_rows, &ret_c, false, span);
                self.scope = saved;
                let sub = sub?;
                self.tc.zonk_locals();
                let sub = self.tc.zonk(&sub);
                let body = if top || !others.is_empty() {
                    self.tc.mk_lam(&others, &sub)
                } else {
                    sub
                };
                let body = match cb {
                    Some(b2) => self.tc.mk_lam(&[b2], &body),
                    None => body,
                };
                let binders: Vec<u32> = fields.iter().chain(&ihs).copied().collect();
                let m = self.tc.mk_lam(&binders, &body);
                if mutual_ms.is_some() {
                    self.mutual_minors.push((cname.clone(), m.clone()));
                }
                match &*rty {
                    Term::Pi(_, _, b) => rty = instantiate(b, &m),
                    _ => return err(span, "internal error: malformed recursor type"),
                }
                minors.push(m);
            }
        }
        let mut args = fam_params.to_vec();
        args.extend(motives_all);
        args.extend(minors);
        args.push(fvar(x));
        if let Some((_, bt)) = &deep_ctx {
            args.push(bt.clone());
        }
        args.extend(others.iter().map(|&o| fvar(o)));
        Ok(mk_apps(&cnst(info_rec.clone(), rec_levels), &args))
    }

    /// Prepare course-of-values recursion on the decreasing parameter.
    fn setup_deep(&mut self, ret: &T, span: Span) -> R<Deep> {
        let rc = self.rec.as_ref().expect("recursion context");
        let (decr, explicit) = (rc.decr, rc.explicit.clone());
        let xty = from_kernel(self.tc.local_ty(decr), span)?;
        let xty = self.tc.zonk(&xty);
        let w = from_kernel(self.tc.whnf(&xty), span)?;
        let (h, targs) = app_spine(&w);
        let Term::Const(iname, ilevels) = &*h else {
            return err(span, "cannot recurse on this parameter");
        };
        let iname = iname.to_string();
        let nparams = match self.env.get(&iname) {
            Some(Decl::Inductive(i)) => i.nparams,
            _ => return err(span, "cannot recurse on this parameter"),
        };
        if self.env.get(&format!("{iname}.brecOn")).is_none() {
            return err(
                span,
                format!("`{iname}` has no course-of-values recursor (indexed, mutual or nested?)"),
            );
        }
        let others: Vec<u32> = explicit.iter().copied().filter(|&p| p != decr).collect();
        self.tc.zonk_locals();
        let ret_z = self.tc.zonk(ret);
        let motive_res = self.tc.mk_pi(&others, &ret_z);
        let lvl = from_kernel(self.tc.check_is_type(&motive_res), span)?;
        let lvl = self.tc.zonk_level(&lvl);
        let motive = lam(
            Mult::Omega,
            xty.clone(),
            abstract_fvars(&motive_res, &[decr]),
        );
        let mut levels = vec![lvl];
        levels.extend(ilevels.iter().cloned());
        let params = targs[..nparams].to_vec();
        let mut d = Deep {
            iname,
            levels,
            params,
            motive,
            b: 0,
            below_of: HashMap::new(),
        };
        let below_ty = self.below_type(&d, fvar(decr));
        d.b = self.tc.fresh("b", below_ty, Mult::Omega);
        d.below_of.insert(decr, fvar(d.b));
        Ok(d)
    }

    /// `I.below motive v`.
    fn below_type(&self, d: &Deep, v: T) -> T {
        mk_apps(
            &cnst(
                format!("{}.below", d.iname).as_str().into(),
                d.levels.clone(),
            ),
            &[d.params.clone(), vec![d.motive.clone(), v]].concat(),
        )
    }

    /// `f x others := I.brecOn x (fun x b others => body) others`.
    fn wrap_brec(&mut self, d: &Deep, decr: u32, explicit: &[u32], body: T) -> R<T> {
        let others: Vec<u32> = explicit.iter().copied().filter(|&p| p != decr).collect();
        self.tc.zonk_locals();
        let body = self.tc.zonk(&body);
        let step = self
            .tc
            .mk_lam(&[vec![decr, d.b], others.clone()].concat(), &body);
        let args = [
            d.params.clone(),
            vec![d.motive.clone(), fvar(decr), step],
            others.iter().map(|&o| fvar(o)).collect(),
        ]
        .concat();
        Ok(mk_apps(
            &cnst(
                format!("{}.brecOn", d.iname).as_str().into(),
                d.levels.clone(),
            ),
            &args,
        ))
    }

    /// Split `b : below motive (c fields)` into the (result, below) pair of each
    /// recursive field, in order.
    fn below_components(&mut self, b: u32, n: usize, span: Span) -> R<Vec<(T, T)>> {
        let mut cur = fvar(b);
        let mut out = Vec::new();
        let pprod = |ls: &[Level], name: &str| cnst(name.into(), ls.to_vec());
        for _ in 0..n {
            let ty = from_kernel(self.tc.infer(&cur), span)?;
            let w = from_kernel(self.tc.whnf(&ty), span)?;
            let (h, args) = app_spine(&w);
            let (Term::Const(c, ls), 2) = (&*h, args.len()) else {
                return err(span, "internal error: `below` is not a tuple");
            };
            if &**c != "PProd" {
                return err(span, "internal error: `below` is not a tuple");
            }
            let pair = mk_apps(
                &pprod(ls, "PProd.fst"),
                &[args[0].clone(), args[1].clone(), cur.clone()],
            );
            let rest = mk_apps(
                &pprod(ls, "PProd.snd"),
                &[args[0].clone(), args[1].clone(), cur.clone()],
            );
            let pty = from_kernel(self.tc.infer(&pair), span)?;
            let pw = from_kernel(self.tc.whnf(&pty), span)?;
            let (ph, pargs) = app_spine(&pw);
            let (Term::Const(pc, pls), 2) = (&*ph, pargs.len()) else {
                return err(span, "internal error: `below` element is not a pair");
            };
            if &**pc != "PProd" {
                return err(span, "internal error: `below` element is not a pair");
            }
            let ih = mk_apps(
                &pprod(pls, "PProd.fst"),
                &[pargs[0].clone(), pargs[1].clone(), pair.clone()],
            );
            let bt = mk_apps(
                &pprod(pls, "PProd.snd"),
                &[pargs[0].clone(), pargs[1].clone(), pair],
            );
            out.push((ih, bt));
            cur = rest;
        }
        Ok(out)
    }

    /// Rewrite constructor applications that a nested `match` introduced back to the
    /// field variables they stand for, innermost first: `succ(succ(m))` becomes the
    /// field bound by the outer split when `succ(m)` is the inner field.
    fn canon_fields(&self, t: &T) -> T {
        let refined: Vec<(T, u32)> = match &self.rec {
            Some(rc) => rc
                .refined
                .iter()
                .map(|(c, x)| (self.tc.zonk(c), *x))
                .collect(),
            None => return t.clone(),
        };
        fn go(t: &T, refined: &[(T, u32)]) -> T {
            let t2 = match &**t {
                Term::App(f, a) => app(go(f, refined), go(a, refined)),
                _ => t.clone(),
            };
            match refined.iter().find(|(c, _)| *c == t2) {
                Some((_, x)) => fvar(*x),
                None => t2,
            }
        }
        go(t, &refined)
    }

    /// `f(args)` inside the body of a structurally recursive `f`: becomes the
    /// induction hypothesis of the matched parameter's field.
    fn is_rec_name(&self, p: &str) -> bool {
        self.rec.as_ref().is_some_and(|r| {
            r.name == p
                || r.mutual
                    .as_ref()
                    .is_some_and(|m| m.siblings.iter().any(|(n, _)| n == p))
        })
    }

    fn elab_rec_call(&mut self, name: &str, args: &[Expr], exp: Option<&T>, span: Span) -> R<T> {
        if let Some(wf) = self.rec.as_ref().and_then(|rc| rc.wf.clone()) {
            return self.elab_wf_call(wf, args, exp, span);
        }
        let rc = self.rec.as_ref().expect("recursion context");
        let (decr, explicit) = (rc.decr, rc.explicit.clone());
        // a call of another function of the `mutual` group: it decreases on its first argument
        let sibling = if rc.name == name {
            None
        } else {
            rc.mutual
                .as_ref()
                .and_then(|m| m.siblings.iter().find(|(n, _)| n == name).map(|(_, k)| *k))
        };
        let nargs = sibling.unwrap_or(explicit.len());
        if args.len() != nargs {
            return err(
                span,
                "a recursive call must supply all of the function's arguments",
            );
        }
        let k = if sibling.is_some() {
            0
        } else {
            explicit
                .iter()
                .position(|&p| p == decr)
                .expect("decreasing parameter is explicit")
        };
        let dty = from_kernel(self.tc.local_ty(decr), span)?;
        // a field of an indexed family has other indices than the parameter
        let arg = if sibling.is_some() || self.is_indexed(decr) {
            self.elab(&args[k], None)?
        } else {
            self.elab_check(&args[k], &dty)?
        };
        let arg = self.tc.zonk(&arg);
        let arg = self.canon_fields(&arg);
        let ih = self.rec.as_ref().and_then(|rc| match &*arg {
            Term::FVar(f) => rc.fields.get(f).cloned(),
            _ => rc
                .refined
                .iter()
                .find(|(t, _)| self.tc.zonk(t) == arg)
                .and_then(|(_, x)| rc.fields.get(x).cloned()),
        });
        let Some(ih) = ih else {
            return err(
                args[k].span,
                "this recursive call is not structural: its argument must be a field bound by matching on the parameter",
            );
        };
        let rest: Vec<Arg> = args
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != k)
            .map(|(_, a)| Arg::Expr(a))
            .collect();
        self.elab_app((ih, vec![]), rest, exp, span)
    }

    fn elab_if(
        &mut self,
        cond: &Expr,
        then: &Block,
        els: Option<&Expr>,
        exp: Option<&T>,
        span: Span,
    ) -> R<T> {
        let do_mode = std::mem::take(&mut self.do_mode);
        let bool_ty = cnst("Bool".into(), vec![]);
        let c = self.elab_check(cond, &bool_ty)?;
        let vars = self.state_vars();
        let then_branch = |cx: &mut Self, r: Option<&T>| -> R<T> {
            if do_mode {
                let io = r.cloned().expect("a `do` branch has an expected type");
                cx.elab_do(then, Some(&io), then.span)
            } else {
                cx.elab_block_opts(then, r, true)
            }
        };
        let else_branch = |cx: &mut Self, e: &Expr, r: &T| -> R<T> {
            if do_mode {
                cx.elab_action(e, r)
            } else {
                cx.elab_check(e, r)
            }
        };
        if vars.is_empty() || do_mode {
            // (in a `do` statement the variables were already threaded through the
            // branches by the desugaring in `do_stmts`; here they are only restored)
            let saved = self.state_terms(&vars);
            // with `dep_if`, each branch sees the condition as a hypothesis `c = true/false`
            let hyps = if self.dep_if {
                let bool_t = cnst("Bool".into(), vec![]);
                let eq = |b: &str| {
                    mk_apps(
                        &cnst("Eq".into(), vec![Level::of_nat(1)]),
                        &[bool_t.clone(), c.clone(), cnst(b.into(), vec![])],
                    )
                };
                let (tt, ft) = (eq("Bool.true"), eq("Bool.false"));
                Some((
                    self.tc.fresh("hc", tt, Mult::Omega),
                    self.tc.fresh("hc", ft, Mult::Omega),
                ))
            } else {
                None
            };
            let depth = self.scope.len();
            if let Some((ht, _)) = hyps {
                self.scope.push(("_hc".into(), fvar(ht)));
            }
            let then_t = self.scoped(|cx| then_branch(cx, exp));
            self.scope.truncate(depth);
            let then_t = then_t?;
            self.restore_state(&vars, &saved);
            let ty = match exp {
                Some(t) => t.clone(),
                None => from_kernel(self.tc.infer(&then_t), then.span)?,
            };
            let then_t = self.coerce(then_t, &ty, then.span)?;
            if let Some((_, hf)) = hyps {
                self.scope.push(("_hc".into(), fvar(hf)));
            }
            let else_t = match els {
                Some(e) => self.scoped(|cx| else_branch(cx, e, &ty)),
                None => {
                    let u = self.unit_branch(&ty, do_mode);
                    self.coerce(u, &ty, span)
                }
            };
            self.scope.truncate(depth);
            let else_t = else_t?;
            self.restore_state(&vars, &saved);
            if let Some((ht, hf)) = hyps {
                return self.build_dep_if(c, &ty, then_t, else_t, (ht, hf), span);
            }
            return self.build_if(c, &ty, then_t, else_t, span);
        }
        // mutable variables are in scope: each branch returns its value together
        // with the variables as it leaves them, and they are rebound afterwards
        let r = match exp {
            Some(t) => t.clone(),
            None => self.fresh_type(span),
        };
        let tys = self.state_types(&vars)?;
        let st = StateCtx {
            r: r.clone(),
            vars: vars.clone(),
            tys: tys.clone(),
        };
        let saved = self.state_terms(&vars);
        let then_t = self.scoped(|cx| {
            let v = then_branch(cx, Some(&st.r))?;
            let v = cx.coerce(v, &st.r, then.span)?;
            Ok(cx.state_pair(&st, v))
        })?;
        self.restore_state(&vars, &saved);
        let else_t = self.scoped(|cx| {
            let v = match els {
                Some(e) => else_branch(cx, e, &st.r)?,
                None => {
                    let u = cx.unit_branch(&st.r, do_mode);
                    cx.coerce(u, &st.r, span)?
                }
            };
            Ok(cx.state_pair(&st, v))
        })?;
        self.restore_state(&vars, &saved);
        let pair_ty = prod_ty(&r, &tuple_ty(&tys));
        let pair = self.build_if(c, &pair_ty, then_t, else_t, span)?;
        Ok(self.rebind_state(&st, &pair_ty, pair))
    }

    /// The value of an omitted `else`: `()`, or `pure(())` in a `do` block.
    fn unit_branch(&self, _ty: &T, do_mode: bool) -> T {
        if do_mode {
            mk_apps(
                &cnst("IO.pure".into(), vec![]),
                &[self.unit_type(), self.unit_value()],
            )
        } else {
            self.unit_value()
        }
    }

    /// `Bool.rec (fun _ => ty) else_case then_case c`
    /// `if` with the condition as a hypothesis in each branch:
    /// `Bool.rec (fun b => c = b → ty) (fun h => else) (fun h => then) c rfl`.
    fn build_dep_if(
        &mut self,
        c: T,
        ty: &T,
        then_t: T,
        else_t: T,
        (ht, hf): (u32, u32),
        span: Span,
    ) -> R<T> {
        let bool_ty = cnst("Bool".into(), vec![]);
        self.tc.zonk_locals();
        let ty = self.tc.zonk(ty);
        let lvl = from_kernel(self.tc.check_is_type(&ty), span)?;
        let lvl = self.tc.zonk_level(&lvl);
        let c = self.tc.zonk(&c);
        let eq_c_b = mk_apps(
            &cnst("Eq".into(), vec![Level::of_nat(1)]),
            &[bool_ty.clone(), c.clone(), bvar(0)],
        );
        let motive = lam(Mult::Omega, bool_ty.clone(), pi(Mult::Omega, eq_c_b, ty));
        let then_l = self.tc.mk_lam(&[ht], &self.tc.zonk(&then_t));
        let else_l = self.tc.mk_lam(&[hf], &self.tc.zonk(&else_t));
        let refl = mk_apps(
            &cnst("Eq.refl".into(), vec![Level::of_nat(1)]),
            &[bool_ty, c.clone()],
        );
        let rec = cnst("Bool.rec".into(), vec![lvl]);
        Ok(mk_apps(&rec, &[motive, else_l, then_l, c, refl]))
    }

    fn build_if(&mut self, c: T, ty: &T, then_t: T, else_t: T, span: Span) -> R<T> {
        let bool_ty = cnst("Bool".into(), vec![]);
        let ty = self.tc.zonk(ty);
        let lvl = from_kernel(self.tc.check_is_type(&ty), span)?;
        let lvl = self.tc.zonk_level(&lvl);
        let motive = lam(Mult::Omega, bool_ty, ty);
        let rec = cnst("Bool.rec".into(), vec![lvl]);
        Ok(mk_apps(&rec, &[motive, else_t, then_t, c]))
    }
}

fn mentions_expr(e: &Expr, name: &str) -> bool {
    match &e.kind {
        ExprKind::Var(n) => n == name,
        ExprKind::Nat(_) | ExprKind::Str(_) | ExprKind::Wild | ExprKind::Unit => false,
        ExprKind::Neg(a) | ExprKind::Deref(a) => mentions_expr(a, name),
        ExprKind::Ascribe(a, t) => mentions_expr(a, name) || mentions_expr(t, name),
        ExprKind::By(_) => false,
        ExprKind::Binary(_, a, b) | ExprKind::Arrow(a, b) => {
            mentions_expr(a, name) || mentions_expr(b, name)
        }
        ExprKind::Forall(bs, body) => {
            bs.iter().any(|(_, t)| mentions_expr(t, name)) || mentions_expr(body, name)
        }
        ExprKind::Ref { inner, .. } => mentions_expr(inner, name),
        ExprKind::Call(f, args) | ExprKind::TypeApp(f, args) => {
            mentions_expr(f, name) || args.iter().any(|a| mentions_expr(a, name))
        }
        ExprKind::Field(b, _) => mentions_expr(b, name),
        ExprKind::Block(b) | ExprKind::Do(b) => mentions_block(b, name),
        ExprKind::List(items) => items.iter().any(|a| mentions_expr(a, name)),
        ExprKind::Lambda { body, .. } => mentions_expr(body, name),
        ExprKind::For { iter, body, .. } => mentions_expr(iter, name) || mentions_block(body, name),
        ExprKind::If(c, t, e) => {
            mentions_expr(c, name)
                || mentions_block(t, name)
                || e.as_ref().is_some_and(|e| mentions_expr(e, name))
        }
        ExprKind::Match(s, arms) => {
            mentions_expr(s, name) || arms.iter().any(|a| mentions_expr(&a.body, name))
        }
    }
}

fn mentions_block(b: &Block, name: &str) -> bool {
    b.stmts.iter().any(|s| match s {
        Stmt::Let { init, .. } => mentions_expr(init, name),
        Stmt::Bind { action, .. } => mentions_expr(action, name),
        Stmt::Assign { target, value, .. } => {
            mentions_expr(target, name) || mentions_expr(value, name)
        }
        Stmt::Expr(e) => mentions_expr(e, name),
    }) || b.tail.as_ref().is_some_and(|t| mentions_expr(t, name))
}

fn flatten_add<'e>(e: &'e Expr, out: &mut Vec<&'e Expr>) {
    match &e.kind {
        ExprKind::Binary(BinOp::Add, a, b) => {
            flatten_add(a, out);
            flatten_add(b, out);
        }
        _ => out.push(e),
    }
}

fn collect_level_params(t: &T, out: &mut Vec<Name>) {
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
        _ => {}
    }
}
