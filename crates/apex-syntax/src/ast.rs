//! Surface syntax tree. Types are ordinary expressions (dependent types).

use crate::lexer::Token;
use apex_span::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Module {
    pub items: Vec<Item>,
    /// Operators and macros this file declares (needed to parse its tactic blocks later).
    pub notations: Notations,
}

/// User-declared syntax. Binding power `lbp` of an operator, whether it associates to
/// the right, and the function it calls; macros are parameter lists with a template.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Notations {
    pub infix: std::collections::HashMap<String, (u8, bool, String)>,
    pub prefix: std::collections::HashMap<String, (u8, String)>,
    pub macros: std::collections::HashMap<String, (Vec<String>, Expr)>,
    /// `tactic name(params) { tokens }`: user-defined tactics (token substitution).
    pub tactics: std::collections::HashMap<String, (Vec<String>, Vec<Token>)>,
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
    /// `mutual { enum A .. enum B .. }`
    Mutual(Vec<Item>),
    /// `universe u v;`: universe level names usable in `Type(u)` / `Sort(u)`.
    Universe(Vec<Ident>),
    /// `import a.b;`: the module `a/b.apex`, loaded by the driver before this file.
    Import(String),
    /// `infixl 65 "+++" => f;`, `prefix 100 "~" => g;`, `macro m(a, b) => e;`: already applied
    /// by the parser; kept so tools can list them.
    Notation(String),
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
    /// A trait parameter written `out C`: determined by the implementation, not by the use.
    pub out: bool,
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
    Nat(u128),
    Str(String),
    Wild,
    Unit,
    Neg(Box<Expr>),
    /// `(e : T)`: elaborate `e` against the type `T`.
    Ascribe(Box<Expr>, Box<Expr>),
    /// `by { tactics }` as a term: a proof of the expected type.
    By(Vec<Tactic>),
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

/// A destructuring pattern of `rcases` / `obtain` / `rintro`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RPat {
    /// Name the hypothesis (`rfl` substitutes an equation instead).
    Name(String),
    Wild,
    /// `(p1, p2, ..)`: the fields of a one-constructor type (`And`, `Exists`, structures).
    Tuple(Vec<RPat>),
    /// `p1 | p2`: one pattern per constructor (`Or`).
    Alt(Vec<RPat>),
}

/// A navigation step of `conv`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NavStep {
    Lhs,
    Rhs,
    /// The `k`-th explicit argument (from 1) of the focused application.
    Arg(usize),
    /// The function part of the focused application (without its last argument).
    Fun,
}

/// One step `a = b := proof` of a `calc` chain (`_` stands for the previous right side).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CalcStep {
    pub rel: Expr,
    pub proof: HaveProof,
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
    /// `cases h : e with { .. }` on a non-variable `e`: split on its value, keeping `h : e = c`.
    CasesEq(Ident, Expr, Option<Vec<CaseArm>>),
    /// `generalize h : e = x`: replace `e` in the goal by a new variable `x`, keeping `h : e = x`.
    Generalize(Option<Ident>, Expr, Ident),
    /// Move hypotheses back into the goal as premises.
    Revert(Vec<Ident>),
    /// `injection h with a b`: the field equations of `h : C as = C bs`.
    Injection(Expr, Vec<Ident>),
    /// `subst h` / `subst x`: eliminate a variable using an equation.
    Subst(Ident),
    /// `rcases e with pat` / `obtain pat := e`
    Rcases(Expr, RPat),
    Rintro(Vec<RPat>),
    /// `by_cases h : P`: split on `P` and `¬P` (classical).
    ByCases(Option<Ident>, Expr),
    /// `by_contra h`: assume the negation of the goal, prove `False`.
    ByContra(Option<Ident>),
    /// `specialize h(a, b)`: replace `h` by its instance.
    Specialize(Expr),
    /// `refine e`: `exact` with `_` holes that become new goals.
    Refine(Expr),
    /// `funext x y`: prove `f = g` from `f x = g x`.
    Funext(Vec<Ident>),
    /// `congr`: reduce `f a = f b` to `a = b`.
    Congr,
    /// `calc { a = b := p; _ = c := q }`
    Calc(Vec<CalcStep>),
    /// `conv at h { lhs; arg 2; rw [..] }`: rewrite inside one subterm of the goal (or of `h`).
    Conv(Option<Ident>, Vec<NavStep>, Vec<Tactic>),
    /// `ring`: commutative-semiring identities over `Nat`, by a verified normalizer.
    Ring,
    /// Try `rfl`, `assumption`, `True.intro`, `decide`, `omega`, `simp`.
    Trivial,
    /// `exists w`: prove `Exists p` by giving the witness.
    Exists(Expr),
    /// `{ ... }`: run on the first goal, which it must close.
    Block(Vec<Tactic>),
    /// Tactics in sequence on the first goal and what it produces (a tactic macro's body).
    Seq(Vec<Tactic>),
    /// `try t`: `t`, or nothing if it fails.
    Try(Box<Tactic>),
    /// `repeat t`: `t` on the goal and on every goal it produces, until it fails.
    Repeat(Box<Tactic>),
    /// `first | t1 | t2`: the first alternative that works.
    First(Vec<Tactic>),
    /// `all_goals t`: on every goal; fails if it fails on any.
    AllGoals(Box<Tactic>),
    /// `any_goals t`: on every goal; fails only if it fails on all.
    AnyGoals(Box<Tactic>),
    /// `t1 <;> t2`: `t2` on every goal `t1` produces.
    Then(Box<Tactic>, Box<Tactic>),
    Skip,
    /// Fails if any goal remains.
    Done,
    Fail(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HaveProof {
    Term(Expr),
    Tactic(Vec<Tactic>),
}
