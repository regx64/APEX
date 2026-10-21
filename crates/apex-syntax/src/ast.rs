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
    pub fields: Vec<Field>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Variant {
    pub name: Ident,
    pub fields: Vec<Expr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnumDecl {
    pub name: Ident,
    pub generics: Vec<Generic>,
    pub variants: Vec<Variant>,
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
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Ref {
        mutable: bool,
        lifetime: Option<String>,
        inner: Box<Expr>,
    },
    /// Function type `A -> B`.
    Arrow(Box<Expr>, Box<Expr>),
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
