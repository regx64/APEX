//! Surface syntax tree. Types are ordinary expressions (dependent types).

use crate::lexer::Token;
use apex_span::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Module {
    pub items: Vec<Item>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Item {
    pub kind: ItemKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ItemKind {
    Fn(FnDecl),
    Struct(StructDecl),
    Enum(EnumDecl),
    Trait(TraitDecl),
    Impl(ImplDecl),
    Theorem(TheoremDecl),
    /// `namespace A.B { .. }`: `fn`s and `theorem`s declared inside get the prefix `A.B.`
    Namespace {
        name: String,
        items: Vec<Item>,
    },
    /// `open A.B;`: names of the namespace can be used unqualified.
    Open(String),
    /// `section { variable (n: Nat); .. }`: scopes `open` and `variable`.
    Section(Vec<Item>),
    /// `variable (n: Nat);` adds `n` as a leading parameter of every later declaration that mentions it.
    Variable(Vec<Param>),
    /// `import a.b;`: the module `a/b.apex`, loaded by the driver before this file.
    Import(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ident {
    pub name: String,
    pub span: Span,
}

/// `T`, `n: Nat`, or a lifetime `'a` (name includes the quote).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Generic {
    pub name: Ident,
    pub ty: Option<Expr>,
}

/// `Own` is a linear (multiplicity 1) parameter; `Default` is inferred from the type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Default,
    Own,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Param {
    pub mode: Mode,
    pub name: Ident,
    pub ty: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnDecl {
    pub name: Ident,
    pub generics: Vec<Generic>,
    pub params: Vec<Param>,
    pub ret: Option<Expr>,
    /// `None` for a signature ending in `;` (trait methods).
    pub body: Option<Block>,
    /// `termination_by e` (and `decreasing_by { .. }`): recursion on a measure.
    pub wf: Option<WfSpec>,
}

/// Well-founded recursion: a `Nat`-valued measure that must decrease on every
/// recursive call, and the tactic proof of that (default: `omega`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WfSpec {
    pub measure: Expr,
    pub decreasing: Option<Vec<Token>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Field {
    pub name: Ident,
    pub ty: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructDecl {
    pub name: Ident,
    pub generics: Vec<Generic>,
    /// `struct B extends A { .. }`: the fields of `A` come first.
    pub parent: Option<Expr>,
    pub fields: Vec<Field>,
    /// `#[derive(BEq, Show)]`
    pub derives: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Variant {
    pub name: Ident,
    /// Constructor-local implicit binders: `Add2<k: Nat>(Even(k)): Even(k + 2)`.
    pub generics: Vec<Generic>,
    pub fields: Vec<Expr>,
    /// The result type when the family is indexed: `: Even(k + 2)`.
    pub result: Option<Expr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnumDecl {
    pub name: Ident,
    pub generics: Vec<Generic>,
    /// Indices of an indexed family: `enum Vec<T>(n: Nat)`.
    pub indices: Vec<(Ident, Expr)>,
    /// `: Prop` makes an inductive predicate (default `Type`).
    pub sort: Option<Expr>,
    pub variants: Vec<Variant>,
    /// `#[derive(BEq, Show)]`
    pub derives: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraitDecl {
    pub name: Ident,
    pub generics: Vec<Generic>,
    pub fns: Vec<FnDecl>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImplDecl {
    pub generics: Vec<Generic>,
    pub trait_ref: Option<Expr>,
    pub self_ty: Expr,
    pub fns: Vec<FnDecl>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoremDecl {
    /// `#[simp]`: `simp` uses this theorem as a rewrite rule.
    pub simp: bool,
    pub name: Ident,
    pub generics: Vec<Generic>,
    pub params: Vec<Param>,
    pub stmt: Expr,
    pub proof: Proof,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Proof {
    Term(Expr),
    /// Raw tokens inside `by { ... }`; parsed by the tactic framework (M6).
    Tactic(Vec<Token>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub tail: Option<Box<Expr>>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    Let {
        mutable: bool,
        name: Ident,
        ty: Option<Expr>,
        init: Expr,
    },
    /// `let x <- action;` (only meaningful inside `do`).
    Bind {
        name: Ident,
        ty: Option<Expr>,
        action: Expr,
    },
    /// `place = value;` or `place op= value;`
    Assign {
        target: Expr,
        op: Option<BinOp>,
        value: Expr,
    },
    Expr(Expr),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arm {
    pub pat: Expr,
    pub body: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LamParam {
    pub name: Ident,
    pub ty: Option<Expr>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    /// Propositional equality `=`.
    Eq,
    /// Boolean equality `==`.
    EqEq,
    Lt,
    Gt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprKind {
    Var(String),
    Nat(u64),
    Str(String),
    Wild,
    Unit,
    Neg(Box<Expr>),
    /// `*e`: dereference (a no-op for value-semantic references).
    Deref(Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Ref {
        mutable: bool,
        lifetime: Option<String>,
        inner: Box<Expr>,
    },
    /// Function type `A -> B`.
    Arrow(Box<Expr>, Box<Expr>),
    /// `forall(x: A, y: B) -> T`: a dependent function type.
    Forall(Vec<(Ident, Expr)>, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    /// Generic application in type position: `Vec<T, n>`.
    TypeApp(Box<Expr>, Vec<Expr>),
    Field(Box<Expr>, Ident),
    Block(Block),
    /// `do { .. }`: a sequence of monadic actions.
    Do(Block),
    /// `[a, b, c]`
    List(Vec<Expr>),
    /// `|x, y: T| body`
    Lambda {
        params: Vec<LamParam>,
        body: Box<Expr>,
    },
    /// `for x in xs { .. }` (inside `do`)
    For {
        var: Ident,
        iter: Box<Expr>,
        body: Block,
    },
    If(Box<Expr>, Block, Option<Box<Expr>>),
    Match(Box<Expr>, Vec<Arm>),
}

/// A tactic in a `by { ... }` block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tactic {
    pub kind: TacticKind,
    pub span: Span,
}

/// A `ctor(a, b) => { tactics }` arm of `induction x with { .. }` / `cases x with { .. }`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CaseArm {
    pub ctor: Ident,
    pub binders: Vec<Ident>,
    pub body: Vec<Tactic>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TacticKind {
    Intro(Vec<Ident>),
    Exact(Expr),
    Apply(Expr),
    Rfl,
    Assumption,
    Constructor,
    Left,
    Right,
    Exfalso,
    Contradiction,
    Symm,
    Decide,
    Omega,
    /// `auto`: a small backtracking proof search.
    Auto,
    Show(Expr),
    Have {
        name: Ident,
        ty: Expr,
        proof: HaveProof,
    },
    /// Rewrite rules; `true` means right-to-left (`<- h`).
    Rw(Vec<(bool, Expr)>, Option<Ident>),
    Simp(Vec<Expr>, Option<Ident>),
    /// `simp only [..]`: just the given rules, no `#[simp]` library.
    SimpOnly(Vec<Expr>, Option<Ident>),
    /// `simp_arith`: `simp`, then `omega` on what is left.
    SimpArith(Vec<Expr>),
    /// `simp_all`: `simp` with every equation among the hypotheses as a rule.
    SimpAll(Vec<Expr>),
    Unfold(Vec<Ident>),
    /// `induction x generalizing a b with { .. }`
    Induction(Ident, Vec<Ident>, Option<Vec<CaseArm>>),
    /// `cases h` or `cases f(x)` (the proof term is first introduced as a hypothesis)
    Cases(Expr, Option<Vec<CaseArm>>),
    /// Move hypotheses back into the goal as premises.
    Revert(Vec<Ident>),
    /// `exists w`: prove `Exists p` by giving the witness.
    Exists(Expr),
    /// `{ ... }`: run on the first goal, which it must close.
    Block(Vec<Tactic>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HaveProof {
    Term(Expr),
    Tactic(Vec<Tactic>),
}
