//! Recursive-descent parser with a Pratt expression core.
//!
//! `<` is ambiguous between comparison and generic arguments. In *type mode*
//! (after `:` / `->` in signatures) it starts generic arguments; elsewhere it
//! is comparison. Parentheses and blocks switch back to value mode.

use crate::ast::*;
use crate::lexer::{lex, Token, TokenKind as T};
use apex_span::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub msg: String,
    pub span: Span,
}

type PResult<X> = Result<X, ParseError>;

/// Lex and parse a whole source file.
pub fn parse(src: &str) -> PResult<Module> {
    let toks = lex(src).map_err(|e| ParseError {
        msg: e.msg,
        span: e.span,
    })?;
    Parser {
        toks,
        pos: 0,
        ty_mode: false,
        nt: Notations::default(),
    }
    .module()
}

/// Parse the tokens of a `by { ... }` block (without the braces).
pub fn parse_tactics(toks: &[Token], end: Span, nt: &Notations) -> PResult<Vec<Tactic>> {
    let mut toks = toks.to_vec();
    toks.push(Token {
        kind: T::Eof,
        span: end,
    });
    let mut p = Parser {
        toks,
        pos: 0,
        ty_mode: false,
        nt: nt.clone(),
    };
    let v = p.tactic_seq()?;
    if *p.peek() != T::Eof {
        return p.err(format!("unexpected {} in tactic block", p.peek()));
    }
    Ok(v)
}

/// Words that start a tactic; they cannot be used as binder names after `intro`.
const TACTIC_WORDS: &[&str] = &[
    "intro",
    "exact",
    "apply",
    "rfl",
    "assumption",
    "constructor",
    "left",
    "right",
    "exfalso",
    "contradiction",
    "symm",
    "decide",
    "omega",
    "auto",
    "linarith",
    "show",
    "have",
    "rw",
    "simp",
    "simp_arith",
    "simp_all",
    "unfold",
    "induction",
    "cases",
    "revert",
    "injection",
    "subst",
    "rcases",
    "obtain",
    "rintro",
    "by_cases",
    "by_contra",
    "specialize",
    "refine",
    "funext",
    "congr",
    "calc",
    "trivial",
    "change",
    "try",
    "repeat",
    "first",
    "all_goals",
    "any_goals",
    "skip",
    "done",
    "fail",
    "exists",
    "generalizing",
    "with",
    "at",
];

struct Parser {
    toks: Vec<Token>,
    pos: usize,
    ty_mode: bool,
    /// Operators and macros declared so far.
    nt: Notations,
}

/// The operators every file has: binding power, right associativity, function.
fn builtin_infix(op: &str) -> Option<(u8, bool, &'static str)> {
    Some(match op {
        "<->" => (2, true, "Iff"),
        "\\/" => (8, true, "Or"),
        "/\\" => (10, true, "And"),
        "<=" => (12, false, "le"),
        ">=" => (12, false, "ge"),
        "!=" => (12, false, "ne"),
        _ => return None,
    })
}

enum Infix {
    Arrow,
    Bin(BinOp),
    /// A declared operator: calls the named function.
    Custom(String),
}

impl Parser {
    fn peek(&self) -> &T {
        &self.toks[self.pos].kind
    }

    fn span(&self) -> Span {
        self.toks[self.pos].span
    }

    fn prev_span(&self) -> Span {
        self.toks[self.pos.saturating_sub(1)].span
    }

    fn bump(&mut self) -> Token {
        let t = self.toks[self.pos].clone();
        if self.pos < self.toks.len() - 1 {
            self.pos += 1;
        }
        t
    }

    fn eat(&mut self, k: &T) -> bool {
        if self.peek() == k {
            self.bump();
            true
        } else {
            false
        }
    }

    fn err<X>(&self, msg: impl Into<String>) -> PResult<X> {
        Err(ParseError {
            msg: msg.into(),
            span: self.span(),
        })
    }

    fn expect(&mut self, k: &T) -> PResult<Span> {
        if self.peek() == k {
            Ok(self.bump().span)
        } else {
            self.err(format!("expected {k}, found {}", self.peek()))
        }
    }

    fn with_mode<R>(&mut self, mode: bool, f: impl FnOnce(&mut Self) -> R) -> R {
        let old = std::mem::replace(&mut self.ty_mode, mode);
        let r = f(self);
        self.ty_mode = old;
        r
    }

    fn ty(&mut self) -> PResult<Expr> {
        self.with_mode(true, |p| p.expr_bp(0))
    }

    fn expr(&mut self) -> PResult<Expr> {
        self.with_mode(false, |p| p.expr_bp(0))
    }

    // ---- tactics ----

    fn tactic_seq(&mut self) -> PResult<Vec<Tactic>> {
        let mut out = Vec::new();
        loop {
            while self.eat(&T::Semi) {}
            if matches!(self.peek(), T::Eof | T::RBrace) {
                return Ok(out);
            }
            out.push(self.tactic()?);
        }
    }

    /// An optional `at h` after `rw [..]` / `simp [..]`.
    fn at_clause(&mut self) -> PResult<Option<Ident>> {
        match self.peek() {
            T::Ident(w) if w == "at" => {
                self.bump();
                Ok(Some(self.ident()?))
            }
            _ => Ok(None),
        }
    }

    fn tactic_block(&mut self) -> PResult<Vec<Tactic>> {
        self.expect(&T::LBrace)?;
        let v = self.tactic_seq()?;
        self.expect(&T::RBrace)?;
        Ok(v)
    }

    fn binder_names(&mut self) -> PResult<Vec<Ident>> {
        let mut out = Vec::new();
        loop {
            match self.peek() {
                T::Ident(n) if !TACTIC_WORDS.contains(&n.as_str()) => out.push(self.ident()?),
                T::Underscore => {
                    let span = self.bump().span;
                    out.push(Ident {
                        name: "_".into(),
                        span,
                    });
                }
                _ => return Ok(out),
            }
        }
    }

    fn case_arms(&mut self) -> PResult<Option<Vec<CaseArm>>> {
        match self.peek() {
            T::Ident(w) if w == "with" => {
                self.bump();
            }
            _ => return Ok(None),
        }
        self.expect(&T::LBrace)?;
        let mut arms = Vec::new();
        while *self.peek() != T::RBrace {
            let ctor = self.ident()?;
            let mut binders = Vec::new();
            if self.eat(&T::LParen) {
                while *self.peek() != T::RParen {
                    binders.extend(self.binder_names()?);
                    if !self.eat(&T::Comma) {
                        break;
                    }
                }
                self.expect(&T::RParen)?;
            }
            self.expect(&T::FatArrow)?;
            let body = self.tactic_block()?;
            arms.push(CaseArm {
                ctor,
                binders,
                body,
            });
            self.eat(&T::Comma);
        }
        self.expect(&T::RBrace)?;
        Ok(Some(arms))
    }

    /// A tactic, with `t1 <;> t2` chains.
    fn tactic(&mut self) -> PResult<Tactic> {
        let start = self.span();
        let mut t = self.tactic_primary()?;
        while *self.peek() == T::Lt
            && self
                .toks
                .get(self.pos + 1)
                .is_some_and(|x| x.kind == T::Semi)
            && self.toks.get(self.pos + 2).is_some_and(|x| x.kind == T::Gt)
        {
            self.bump();
            self.bump();
            self.bump();
            let rhs = self.tactic_primary()?;
            t = Tactic {
                kind: TacticKind::Then(Box::new(t), Box::new(rhs)),
                span: start.to(self.prev_span()),
            };
        }
        Ok(t)
    }

    /// A user-defined tactic: expand its body with the arguments substituted.
    fn expand_tactic_macro(&mut self, name: &str) -> PResult<Tactic> {
        use TacticKind as K;
        let start = self.span();
        self.bump();
        let (params, body) = self.nt.tactics[name].clone();
        let mut args: Vec<Vec<Token>> = Vec::new();
        if !params.is_empty() || *self.peek() == T::LParen {
            self.expect(&T::LParen)?;
            let mut depth = 0;
            let mut cur: Vec<Token> = Vec::new();
            loop {
                match self.peek() {
                    T::Eof => return self.err("unclosed `(` in tactic macro call"),
                    T::RParen if depth == 0 => break,
                    T::Comma if depth == 0 => {
                        args.push(std::mem::take(&mut cur));
                        self.bump();
                        continue;
                    }
                    T::LParen | T::LBracket | T::LBrace => depth += 1,
                    T::RParen | T::RBracket | T::RBrace => depth -= 1,
                    _ => {}
                }
                cur.push(self.bump());
            }
            if !cur.is_empty() || !args.is_empty() {
                args.push(cur);
            }
            self.expect(&T::RParen)?;
        }
        if args.len() != params.len() {
            return self.err(format!(
                "tactic `{name}` takes {} arguments, found {}",
                params.len(),
                args.len()
            ));
        }
        let mut toks = Vec::new();
        for t in &body {
            match &t.kind {
                T::Ident(n) if params.contains(n) => {
                    let a = &args[params.iter().position(|p| p == n).expect("param")];
                    let wrap = a.len() > 1;
                    if wrap {
                        toks.push(Token {
                            kind: T::LParen,
                            span: t.span,
                        });
                    }
                    toks.extend(a.iter().cloned());
                    if wrap {
                        toks.push(Token {
                            kind: T::RParen,
                            span: t.span,
                        });
                    }
                }
                _ => toks.push(t.clone()),
            }
        }
        toks.push(Token {
            kind: T::Eof,
            span: self.prev_span(),
        });
        let mut sub = Parser {
            toks,
            pos: 0,
            ty_mode: false,
            nt: self.nt.clone(),
        };
        let seq = sub.tactic_seq()?;
        if *sub.peek() != T::Eof {
            return sub.err("unexpected token in tactic macro body");
        }
        Ok(Tactic {
            kind: K::Seq(seq),
            span: start.to(self.prev_span()),
        })
    }

    fn tactic_primary(&mut self) -> PResult<Tactic> {
        use TacticKind as K;
        let start = self.span();
        if let T::Ident(w) = self.peek().clone() {
            if self.nt.tactics.contains_key(&w) {
                return self.expand_tactic_macro(&w);
            }
        }
        if *self.peek() == T::LBrace {
            let body = self.tactic_block()?;
            return Ok(Tactic {
                kind: K::Block(body),
                span: start.to(self.prev_span()),
            });
        }
        let word = match self.peek().clone() {
            T::Ident(w) if TACTIC_WORDS.contains(&w.as_str()) => w,
            other => return self.err(format!("expected a tactic, found {other}")),
        };
        self.bump();
        let kind = match word.as_str() {
            "try" => K::Try(Box::new(self.tactic_primary()?)),
            "repeat" => K::Repeat(Box::new(self.tactic_primary()?)),
            "all_goals" => K::AllGoals(Box::new(self.tactic_primary()?)),
            "any_goals" => K::AnyGoals(Box::new(self.tactic_primary()?)),
            "skip" => K::Skip,
            "done" => K::Done,
            "fail" => match self.peek().clone() {
                T::Str(m) => {
                    self.bump();
                    K::Fail(m)
                }
                _ => K::Fail("`fail` tactic".into()),
            },
            "first" => {
                let mut alts = Vec::new();
                while self.eat(&T::Bar) {
                    alts.push(self.tactic_primary()?);
                }
                if alts.is_empty() {
                    return self.err("`first` needs alternatives: `first | t1 | t2`");
                }
                K::First(alts)
            }
            "intro" => K::Intro(self.binder_names()?),
            "exact" => K::Exact(self.expr()?),
            "apply" => K::Apply(self.expr()?),
            "rfl" => K::Rfl,
            "assumption" => K::Assumption,
            "constructor" => K::Constructor,
            "left" => K::Left,
            "right" => K::Right,
            "exfalso" => K::Exfalso,
            "contradiction" => K::Contradiction,
            "symm" => K::Symm,
            "decide" => K::Decide,
            "omega" | "linarith" => K::Omega,
            "auto" => K::Auto,
            "show" => K::Show(self.ty()?),
            "have" => {
                let name = self.ident()?;
                self.expect(&T::Colon)?;
                let ty = self.ty()?;
                self.expect(&T::ColonEq)?;
                let proof = if self.eat(&T::By) {
                    HaveProof::Tactic(self.tactic_block()?)
                } else {
                    HaveProof::Term(self.expr()?)
                };
                K::Have { name, ty, proof }
            }
            "rw" => {
                self.expect(&T::LBracket)?;
                let mut rules = Vec::new();
                while *self.peek() != T::RBracket {
                    let rev = self.eat(&T::LArrow);
                    rules.push((rev, self.expr()?));
                    if !self.eat(&T::Comma) {
                        break;
                    }
                }
                self.expect(&T::RBracket)?;
                K::Rw(rules, self.at_clause()?)
            }
            "simp" | "simp_arith" | "simp_all" => {
                let only = word == "simp" && matches!(self.peek(), T::Ident(w) if w == "only");
                if only {
                    self.bump();
                }
                let mut lemmas = Vec::new();
                if self.eat(&T::LBracket) {
                    while *self.peek() != T::RBracket {
                        lemmas.push(self.expr()?);
                        if !self.eat(&T::Comma) {
                            break;
                        }
                    }
                    self.expect(&T::RBracket)?;
                }
                match word.as_str() {
                    "simp_arith" => K::SimpArith(lemmas),
                    "simp_all" => K::SimpAll(lemmas),
                    _ if only => K::SimpOnly(lemmas, self.at_clause()?),
                    _ => K::Simp(lemmas, self.at_clause()?),
                }
            }
            "unfold" => {
                let names = self.binder_names()?;
                if names.is_empty() {
                    return self.err("`unfold` needs at least one name");
                }
                K::Unfold(names)
            }
            "induction" => {
                let v = self.ident()?;
                let gen = match self.peek() {
                    T::Ident(w) if w == "generalizing" => {
                        self.bump();
                        self.binder_names()?
                    }
                    _ => Vec::new(),
                };
                K::Induction(v, gen, self.case_arms()?)
            }
            "revert" => {
                let names = self.binder_names()?;
                if names.is_empty() {
                    return self.err("`revert` needs at least one name");
                }
                K::Revert(names)
            }
            "exists" => K::Exists(self.expr()?),
            "subst" => K::Subst(self.ident()?),
            "change" => K::Show(self.ty()?),
            "trivial" => K::Trivial,
            "congr" => K::Congr,
            "refine" => K::Refine(self.expr()?),
            "specialize" => K::Specialize(self.expr()?),
            "funext" => K::Funext(self.binder_names()?),
            "by_contra" => K::ByContra(match self.peek() {
                T::Ident(w) if !TACTIC_WORDS.contains(&w.as_str()) => Some(self.ident()?),
                _ => None,
            }),
            "by_cases" => {
                // `by_cases h : P` or `by_cases P`
                let named = matches!(self.peek(), T::Ident(_))
                    && self
                        .toks
                        .get(self.pos + 1)
                        .is_some_and(|t| t.kind == T::Colon);
                let name = if named {
                    let n = self.ident()?;
                    self.expect(&T::Colon)?;
                    Some(n)
                } else {
                    None
                };
                K::ByCases(name, self.ty()?)
            }
            "rcases" => {
                let e = self.expr()?;
                match self.peek() {
                    T::Ident(w) if w == "with" => {
                        self.bump();
                    }
                    other => return self.err(format!("expected `with`, found {other}")),
                }
                K::Rcases(e, self.rpat_alt()?)
            }
            "obtain" => {
                let pat = self.rpat_alt()?;
                self.expect(&T::ColonEq)?;
                K::Rcases(self.expr()?, pat)
            }
            "rintro" => {
                let mut pats = Vec::new();
                while matches!(self.peek(), T::Underscore | T::LParen)
                    || matches!(self.peek(), T::Ident(w) if !TACTIC_WORDS.contains(&w.as_str()))
                {
                    pats.push(self.rpat_atom()?);
                }
                if pats.is_empty() {
                    return self.err("`rintro` needs at least one pattern");
                }
                K::Rintro(pats)
            }
            "calc" => {
                self.expect(&T::LBrace)?;
                let mut steps = Vec::new();
                while *self.peek() != T::RBrace {
                    let rel = self.expr()?;
                    self.expect(&T::ColonEq)?;
                    let proof = if self.eat(&T::By) {
                        HaveProof::Tactic(self.tactic_block()?)
                    } else {
                        HaveProof::Term(self.expr()?)
                    };
                    steps.push(CalcStep { rel, proof });
                    if !self.eat(&T::Semi) && !self.eat(&T::Comma) {
                        break;
                    }
                }
                self.expect(&T::RBrace)?;
                if steps.is_empty() {
                    return self.err("`calc` needs at least one step");
                }
                K::Calc(steps)
            }
            "injection" => {
                let h = self.expr()?;
                let names = if matches!(self.peek(), T::Ident(w) if w == "with") {
                    self.bump();
                    self.binder_names()?
                } else {
                    Vec::new()
                };
                K::Injection(h, names)
            }
            "cases" => {
                let v = self.expr()?;
                K::Cases(v, self.case_arms()?)
            }
            _ => unreachable!("every tactic word is handled"),
        };
        Ok(Tactic {
            kind,
            span: start.to(self.prev_span()),
        })
    }

    fn rpat_alt(&mut self) -> PResult<RPat> {
        let first = self.rpat_atom()?;
        if *self.peek() != T::Bar {
            return Ok(first);
        }
        let mut alts = vec![first];
        while self.eat(&T::Bar) {
            alts.push(self.rpat_atom()?);
        }
        Ok(RPat::Alt(alts))
    }

    fn rpat_atom(&mut self) -> PResult<RPat> {
        match self.peek().clone() {
            T::Underscore => {
                self.bump();
                Ok(RPat::Wild)
            }
            T::Ident(n) if !TACTIC_WORDS.contains(&n.as_str()) => {
                self.bump();
                Ok(RPat::Name(n))
            }
            T::LParen => {
                self.bump();
                let mut items = vec![self.rpat_alt()?];
                while self.eat(&T::Comma) {
                    items.push(self.rpat_alt()?);
                }
                self.expect(&T::RParen)?;
                Ok(if items.len() == 1 {
                    items.pop().expect("one item")
                } else {
                    RPat::Tuple(items)
                })
            }
            other => self.err(format!("expected a pattern, found {other}")),
        }
    }

    fn ident(&mut self) -> PResult<Ident> {
        match self.peek().clone() {
            T::Ident(name) => Ok(Ident {
                name,
                span: self.bump().span,
            }),
            other => self.err(format!("expected identifier, found {other}")),
        }
    }

    // ---- items ----

    fn module(&mut self) -> PResult<Module> {
        let mut items = Vec::new();
        while *self.peek() != T::Eof {
            items.push(self.item()?);
        }
        Ok(Module {
            items,
            notations: self.nt.clone(),
        })
    }

    fn item(&mut self) -> PResult<Item> {
        let start = self.span();
        let mut simp = false;
        let mut derives: Vec<String> = Vec::new();
        while self.eat(&T::Hash) {
            self.expect(&T::LBracket)?;
            let attr = self.ident()?;
            match attr.name.as_str() {
                "derive" => {
                    self.expect(&T::LParen)?;
                    while *self.peek() != T::RParen {
                        derives.push(self.ident()?.name);
                        if !self.eat(&T::Comma) {
                            break;
                        }
                    }
                    self.expect(&T::RParen)?;
                }
                "simp" => simp = true,
                other => {
                    return Err(ParseError {
                        msg: format!("unknown attribute `{other}` (expected `simp` or `derive`)"),
                        span: attr.span,
                    })
                }
            }
            self.expect(&T::RBracket)?;
        }
        if simp && *self.peek() != T::Theorem {
            return self.err("`#[simp]` can only be applied to a theorem");
        }
        if !derives.is_empty() && !matches!(self.peek(), T::Struct | T::Enum) {
            return self.err("`#[derive(..)]` can only be applied to a struct or an enum");
        }
        let word = match self.peek() {
            T::Ident(w)
                if matches!(
                    w.as_str(),
                    "namespace"
                        | "open"
                        | "section"
                        | "variable"
                        | "import"
                        | "infixl"
                        | "infixr"
                        | "infix"
                        | "prefix"
                        | "macro"
                        | "tactic"
                        | "mutual"
                ) =>
            {
                Some(w.clone())
            }
            _ => None,
        };
        if let Some(w) = word {
            self.bump();
            let kind = match w.as_str() {
                "namespace" => {
                    let name = self.dotted_name()?;
                    ItemKind::Namespace {
                        name,
                        items: self.item_block()?,
                    }
                }
                "open" => {
                    let name = self.dotted_name()?;
                    self.eat(&T::Semi);
                    ItemKind::Open(name)
                }
                "section" => ItemKind::Section(self.item_block()?),
                "mutual" => ItemKind::Mutual(self.item_block()?),
                "infixl" | "infixr" | "infix" | "prefix" => {
                    let prec = match self.peek().clone() {
                        T::Nat(n) => {
                            self.bump();
                            n
                        }
                        _ => 65,
                    };
                    let op = match self.peek().clone() {
                        T::Str(s) => {
                            self.bump();
                            s
                        }
                        other => {
                            return self
                                .err(format!("expected the operator in quotes, found {other}"))
                        }
                    };
                    self.expect(&T::FatArrow)?;
                    let func = self.dotted_name()?;
                    self.eat(&T::Semi);
                    // Lean-style precedence numbers (`=` 50, `+` 65, `*` 70) to our binding powers
                    let lbp = match prec {
                        0..=20 => 2,
                        21..=25 => 4,
                        26..=30 => 8,
                        31..=35 => 10,
                        36..=50 => 12,
                        51..=65 => 14,
                        66..=70 => 16,
                        _ => 18,
                    };
                    if w == "prefix" {
                        self.nt.prefix.insert(op.clone(), (lbp, func));
                    } else {
                        self.nt.infix.insert(op.clone(), (lbp, w == "infixr", func));
                    }
                    ItemKind::Notation(format!("{w} {prec} \"{op}\""))
                }
                "tactic" => {
                    let name = self.ident()?.name;
                    let mut params = Vec::new();
                    if self.eat(&T::LParen) {
                        while *self.peek() != T::RParen {
                            params.push(self.ident()?.name);
                            if !self.eat(&T::Comma) {
                                break;
                            }
                        }
                        self.expect(&T::RParen)?;
                    }
                    let body = self.raw_braced_tokens()?;
                    self.nt.tactics.insert(name.clone(), (params, body));
                    ItemKind::Notation(format!("tactic {name}"))
                }
                "macro" => {
                    let name = self.ident()?.name;
                    self.expect(&T::LParen)?;
                    let mut params = Vec::new();
                    while *self.peek() != T::RParen {
                        params.push(self.ident()?.name);
                        if !self.eat(&T::Comma) {
                            break;
                        }
                    }
                    self.expect(&T::RParen)?;
                    self.expect(&T::FatArrow)?;
                    let body = self.expr()?;
                    self.eat(&T::Semi);
                    self.nt.macros.insert(name.clone(), (params, body));
                    ItemKind::Notation(format!("macro {name}"))
                }
                "import" => {
                    let name = self.dotted_name()?;
                    self.eat(&T::Semi);
                    ItemKind::Import(name)
                }
                _ => {
                    let params = self.params()?;
                    self.eat(&T::Semi);
                    ItemKind::Variable(params)
                }
            };
            return Ok(Item {
                kind,
                span: start.to(self.prev_span()),
            });
        }
        let kind = match self.peek() {
            T::Fn => ItemKind::Fn(self.fn_decl()?),
            T::Struct => {
                let mut d = self.struct_decl()?;
                d.derives = derives;
                ItemKind::Struct(d)
            }
            T::Enum => {
                let mut d = self.enum_decl()?;
                d.derives = derives;
                ItemKind::Enum(d)
            }
            T::Trait => ItemKind::Trait(self.trait_decl()?),
            T::Impl => ItemKind::Impl(self.impl_decl()?),
            T::Theorem => {
                let mut t = self.theorem_decl()?;
                t.simp = simp;
                ItemKind::Theorem(t)
            }
            other => {
                return self.err(format!(
                    "expected an item (`fn`, `struct`, `enum`, `trait`, `impl` or `theorem`), found {other}"
                ))
            }
        };
        Ok(Item {
            kind,
            span: start.to(self.prev_span()),
        })
    }

    /// The tokens between a `{` and its matching `}` (tactic blocks are parsed later).
    fn raw_braced_tokens(&mut self) -> PResult<Vec<Token>> {
        self.expect(&T::LBrace)?;
        let mut depth = 1;
        let mut toks = Vec::new();
        loop {
            match self.peek() {
                T::LBrace => depth += 1,
                T::RBrace => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                T::Eof => return self.err("unclosed `{` in tactic block"),
                _ => {}
            }
            toks.push(self.bump());
        }
        self.expect(&T::RBrace)?;
        Ok(toks)
    }

    fn dotted_name(&mut self) -> PResult<String> {
        let mut name = self.ident()?.name;
        while self.eat(&T::Dot) {
            name.push('.');
            name.push_str(&self.ident()?.name);
        }
        Ok(name)
    }

    fn item_block(&mut self) -> PResult<Vec<Item>> {
        self.expect(&T::LBrace)?;
        let mut items = Vec::new();
        while *self.peek() != T::RBrace {
            if *self.peek() == T::Eof {
                return self.err("unclosed `{`");
            }
            items.push(self.item()?);
        }
        self.expect(&T::RBrace)?;
        Ok(items)
    }

    fn generics(&mut self) -> PResult<Vec<Generic>> {
        let mut out = Vec::new();
        if !self.eat(&T::Lt) {
            return Ok(out);
        }
        while *self.peek() != T::Gt {
            let name = match self.peek().clone() {
                T::Lifetime(name) => Ident {
                    name,
                    span: self.bump().span,
                },
                _ => self.ident()?,
            };
            let ty = if self.eat(&T::Colon) {
                Some(self.ty()?)
            } else {
                None
            };
            out.push(Generic { name, ty });
            if !self.eat(&T::Comma) {
                break;
            }
        }
        self.expect(&T::Gt)?;
        Ok(out)
    }

    fn params(&mut self) -> PResult<Vec<Param>> {
        self.expect(&T::LParen)?;
        let mut out = Vec::new();
        while *self.peek() != T::RParen {
            out.push(self.param()?);
            if !self.eat(&T::Comma) {
                break;
            }
        }
        self.expect(&T::RParen)?;
        Ok(out)
    }

    fn param(&mut self) -> PResult<Param> {
        let start = self.span();
        if self.eat(&T::Amp) {
            // `&self`, `&mut self`, `&'a self`
            let lifetime = match self.peek().clone() {
                T::Lifetime(l) => {
                    self.bump();
                    Some(l)
                }
                _ => None,
            };
            let mutable = self.eat(&T::Mut);
            let name = self.ident()?;
            if name.name != "self" {
                return Err(ParseError {
                    msg: "expected `self` after `&` in parameter".into(),
                    span: name.span,
                });
            }
            let inner = Expr {
                kind: ExprKind::Var("Self".into()),
                span: name.span,
            };
            let ty = Expr {
                kind: ExprKind::Ref {
                    mutable,
                    lifetime,
                    inner: Box::new(inner),
                },
                span: start.to(name.span),
            };
            return Ok(Param {
                mode: Mode::Default,
                name,
                ty,
            });
        }
        let mode = if self.eat(&T::Own) {
            Mode::Own
        } else {
            Mode::Default
        };
        let name = if *self.peek() == T::Underscore {
            Ident {
                name: "_".into(),
                span: self.bump().span,
            }
        } else {
            self.ident()?
        };
        if name.name == "self" && *self.peek() != T::Colon {
            let ty = Expr {
                kind: ExprKind::Var("Self".into()),
                span: name.span,
            };
            return Ok(Param { mode, name, ty });
        }
        self.expect(&T::Colon)?;
        Ok(Param {
            mode,
            name,
            ty: self.ty()?,
        })
    }

    fn fn_decl(&mut self) -> PResult<FnDecl> {
        self.expect(&T::Fn)?;
        let name = self.ident()?;
        let generics = self.generics()?;
        let params = self.params()?;
        let ret = if self.eat(&T::Arrow) {
            Some(self.ty()?)
        } else {
            None
        };
        let mut wf = None;
        if matches!(self.peek(), T::Ident(w) if w == "termination_by") {
            self.bump();
            let measure = self.expr()?;
            let mut decreasing = None;
            if matches!(self.peek(), T::Ident(w) if w == "decreasing_by") {
                self.bump();
                decreasing = Some(self.raw_braced_tokens()?);
            }
            wf = Some(WfSpec {
                measure,
                decreasing,
            });
        }
        let body = if *self.peek() == T::LBrace {
            Some(self.block()?)
        } else {
            self.expect(&T::Semi)?;
            None
        };
        Ok(FnDecl {
            name,
            generics,
            params,
            ret,
            body,
            wf,
        })
    }

    fn struct_decl(&mut self) -> PResult<StructDecl> {
        self.expect(&T::Struct)?;
        let name = self.ident()?;
        let generics = self.generics()?;
        let parent = if matches!(self.peek(), T::Ident(w) if w == "extends") {
            self.bump();
            Some(self.ty()?)
        } else {
            None
        };
        self.expect(&T::LBrace)?;
        let mut fields = Vec::new();
        while *self.peek() != T::RBrace {
            let fname = self.ident()?;
            self.expect(&T::Colon)?;
            fields.push(Field {
                name: fname,
                ty: self.ty()?,
            });
            if !self.eat(&T::Comma) {
                break;
            }
        }
        self.expect(&T::RBrace)?;
        Ok(StructDecl {
            name,
            generics,
            parent,
            fields,
            derives: Vec::new(),
        })
    }

    fn enum_decl(&mut self) -> PResult<EnumDecl> {
        self.expect(&T::Enum)?;
        let name = self.ident()?;
        let generics = self.generics()?;
        let mut indices = Vec::new();
        if self.eat(&T::LParen) {
            while *self.peek() != T::RParen {
                let n = self.ident()?;
                self.expect(&T::Colon)?;
                indices.push((n, self.ty()?));
                if !self.eat(&T::Comma) {
                    break;
                }
            }
            self.expect(&T::RParen)?;
        }
        let sort = if self.eat(&T::Colon) {
            Some(self.ty()?)
        } else {
            None
        };
        self.expect(&T::LBrace)?;
        let mut variants = Vec::new();
        while *self.peek() != T::RBrace {
            let vname = self.ident()?;
            let vgenerics = self.generics()?;
            let mut fields = Vec::new();
            if self.eat(&T::LParen) {
                while *self.peek() != T::RParen {
                    fields.push(self.ty()?);
                    if !self.eat(&T::Comma) {
                        break;
                    }
                }
                self.expect(&T::RParen)?;
            }
            let result = if self.eat(&T::Colon) {
                Some(self.ty()?)
            } else {
                None
            };
            variants.push(Variant {
                name: vname,
                generics: vgenerics,
                fields,
                result,
            });
            if !self.eat(&T::Comma) {
                break;
            }
        }
        self.expect(&T::RBrace)?;
        Ok(EnumDecl {
            name,
            generics,
            indices,
            sort,
            variants,
            derives: Vec::new(),
        })
    }

    fn assoc_fns(&mut self) -> PResult<Vec<FnDecl>> {
        self.expect(&T::LBrace)?;
        let mut fns = Vec::new();
        while *self.peek() != T::RBrace {
            if *self.peek() != T::Fn {
                return self.err(format!("expected `fn` or `}}`, found {}", self.peek()));
            }
            fns.push(self.fn_decl()?);
        }
        self.expect(&T::RBrace)?;
        Ok(fns)
    }

    fn trait_decl(&mut self) -> PResult<TraitDecl> {
        self.expect(&T::Trait)?;
        let name = self.ident()?;
        let generics = self.generics()?;
        Ok(TraitDecl {
            name,
            generics,
            fns: self.assoc_fns()?,
        })
    }

    fn impl_decl(&mut self) -> PResult<ImplDecl> {
        self.expect(&T::Impl)?;
        let generics = self.generics()?;
        let first = self.ty()?;
        let (trait_ref, self_ty) = if self.eat(&T::For) {
            (Some(first), self.ty()?)
        } else {
            (None, first)
        };
        Ok(ImplDecl {
            generics,
            trait_ref,
            self_ty,
            fns: self.assoc_fns()?,
        })
    }

    fn theorem_decl(&mut self) -> PResult<TheoremDecl> {
        self.expect(&T::Theorem)?;
        let name = self.ident()?;
        let generics = self.generics()?;
        let params = self.params()?;
        self.expect(&T::Colon)?;
        // type mode: statements such as `And<P, Q>` take generic arguments
        let stmt = self.ty()?;
        self.expect(&T::ColonEq)?;
        let proof = if self.eat(&T::By) {
            Proof::Tactic(self.raw_braced_tokens()?)
        } else {
            Proof::Term(self.expr()?)
        };
        Ok(TheoremDecl {
            simp: false,
            name,
            generics,
            params,
            stmt,
            proof,
        })
    }

    // ---- statements and blocks ----

    fn block(&mut self) -> PResult<Block> {
        let start = self.expect(&T::LBrace)?;
        self.with_mode(false, |p| {
            let mut stmts = Vec::new();
            let mut tail = None;
            while *p.peek() != T::RBrace {
                if p.eat(&T::Let) {
                    let mutable = p.eat(&T::Mut);
                    let name = p.ident()?;
                    let ty = if p.eat(&T::Colon) {
                        Some(p.ty()?)
                    } else {
                        None
                    };
                    if p.eat(&T::LArrow) {
                        let action = p.expr()?;
                        p.expect(&T::Semi)?;
                        stmts.push(Stmt::Bind { name, ty, action });
                        continue;
                    }
                    p.expect(&T::ColonEq)?;
                    let init = p.expr()?;
                    p.expect(&T::Semi)?;
                    stmts.push(Stmt::Let {
                        mutable,
                        name,
                        ty,
                        init,
                    });
                    continue;
                }
                let e = p.expr()?;
                // `x += e;` and `x = e;` are assignments when the left side is a place
                let compound = match p.peek() {
                    T::PlusEq => Some(BinOp::Add),
                    T::MinusEq => Some(BinOp::Sub),
                    T::StarEq => Some(BinOp::Mul),
                    T::SlashEq => Some(BinOp::Div),
                    T::PercentEq => Some(BinOp::Rem),
                    _ => None,
                };
                if let Some(op) = compound {
                    if !is_place(&e) {
                        return p
                            .err("the left side of an assignment must be a variable or a field");
                    }
                    p.bump();
                    let value = p.expr()?;
                    p.expect(&T::Semi)?;
                    stmts.push(Stmt::Assign {
                        target: e,
                        op: Some(op),
                        value,
                    });
                    continue;
                }
                if let ExprKind::Binary(BinOp::Eq, lhs, rhs) = &e.kind {
                    if is_place(lhs) && *p.peek() == T::Semi {
                        p.bump();
                        stmts.push(Stmt::Assign {
                            target: (**lhs).clone(),
                            op: None,
                            value: (**rhs).clone(),
                        });
                        continue;
                    }
                }
                if p.eat(&T::Semi) || (is_block_like(&e) && *p.peek() != T::RBrace) {
                    stmts.push(Stmt::Expr(e));
                } else if *p.peek() == T::RBrace {
                    tail = Some(Box::new(e));
                } else {
                    return p.err(format!("expected `;` or `}}`, found {}", p.peek()));
                }
            }
            let end = p.expect(&T::RBrace)?;
            Ok(Block {
                stmts,
                tail,
                span: start.to(end),
            })
        })
    }

    // ---- expressions ----

    fn infix(&self) -> Option<(u8, u8, Infix)> {
        Some(match self.peek() {
            T::Arrow => (4, 4, Infix::Arrow),
            T::Eq => (12, 13, Infix::Bin(BinOp::Eq)),
            T::EqEq => (12, 13, Infix::Bin(BinOp::EqEq)),
            T::Lt if !self.ty_mode => (12, 13, Infix::Bin(BinOp::Lt)),
            T::Gt if !self.ty_mode => (12, 13, Infix::Bin(BinOp::Gt)),
            T::Plus => (14, 15, Infix::Bin(BinOp::Add)),
            T::Minus => (14, 15, Infix::Bin(BinOp::Sub)),
            T::Star => (16, 17, Infix::Bin(BinOp::Mul)),
            T::Slash => (16, 17, Infix::Bin(BinOp::Div)),
            T::Percent => (16, 17, Infix::Bin(BinOp::Rem)),
            T::Op(o) => {
                let (lbp, right, f) = match self.nt.infix.get(o) {
                    Some(d) => (d.0, d.1, d.2.as_str()),
                    None => builtin_infix(o)?,
                };
                (
                    lbp,
                    if right { lbp } else { lbp + 1 },
                    Infix::Custom(f.to_string()),
                )
            }
            _ => return None,
        })
    }

    fn expr_bp(&mut self, min: u8) -> PResult<Expr> {
        let mut lhs = self.prefix()?;
        while let Some((lbp, rbp, op)) = self.infix() {
            if lbp < min {
                break;
            }
            self.bump();
            let rhs = self.expr_bp(rbp)?;
            let span = lhs.span.to(rhs.span);
            let kind = match op {
                Infix::Arrow => ExprKind::Arrow(Box::new(lhs), Box::new(rhs)),
                Infix::Bin(b) => ExprKind::Binary(b, Box::new(lhs), Box::new(rhs)),
                Infix::Custom(f) => ExprKind::Call(
                    Box::new(Expr {
                        kind: ExprKind::Var(f),
                        span: lhs.span,
                    }),
                    vec![lhs, rhs],
                ),
            };
            lhs = Expr { kind, span };
        }
        Ok(lhs)
    }

    fn prefix(&mut self) -> PResult<Expr> {
        let start = self.span();
        match self.peek() {
            T::Bar => {
                self.bump();
                let mut params = Vec::new();
                while *self.peek() != T::Bar {
                    let name = self.ident()?;
                    let ty = if self.eat(&T::Colon) {
                        Some(self.ty()?)
                    } else {
                        None
                    };
                    params.push(LamParam { name, ty });
                    if !self.eat(&T::Comma) {
                        break;
                    }
                }
                self.expect(&T::Bar)?;
                let body = self.expr()?;
                Ok(Expr {
                    span: start.to(body.span),
                    kind: ExprKind::Lambda {
                        params,
                        body: Box::new(body),
                    },
                })
            }
            T::Op(o) if self.nt.prefix.contains_key(o) => {
                let (bp, f) = self.nt.prefix[o].clone();
                self.bump();
                let inner = self.expr_bp(bp)?;
                Ok(Expr {
                    span: start.to(inner.span),
                    kind: ExprKind::Call(
                        Box::new(Expr {
                            kind: ExprKind::Var(f),
                            span: start,
                        }),
                        vec![inner],
                    ),
                })
            }
            T::Star => {
                self.bump();
                let inner = self.expr_bp(18)?;
                Ok(Expr {
                    span: start.to(inner.span),
                    kind: ExprKind::Deref(Box::new(inner)),
                })
            }
            T::Minus => {
                self.bump();
                let inner = self.expr_bp(18)?;
                Ok(Expr {
                    span: start.to(inner.span),
                    kind: ExprKind::Neg(Box::new(inner)),
                })
            }
            T::Amp => {
                self.bump();
                let lifetime = match self.peek().clone() {
                    T::Lifetime(l) => {
                        self.bump();
                        Some(l)
                    }
                    _ => None,
                };
                let mutable = self.eat(&T::Mut);
                let inner = self.expr_bp(18)?;
                Ok(Expr {
                    span: start.to(inner.span),
                    kind: ExprKind::Ref {
                        mutable,
                        lifetime,
                        inner: Box::new(inner),
                    },
                })
            }
            _ => {
                let atom = self.atom()?;
                self.postfix(atom)
            }
        }
    }

    fn postfix(&mut self, mut e: Expr) -> PResult<Expr> {
        loop {
            match self.peek() {
                T::LParen => {
                    self.bump();
                    let args = self.with_mode(false, |p| p.comma_list(&T::RParen))?;
                    let end = self.expect(&T::RParen)?;
                    let span = e.span.to(end);
                    // a macro call is replaced by its template with the arguments substituted
                    if let ExprKind::Var(name) = &e.kind {
                        if let Some((params, body)) = self.nt.macros.get(name) {
                            if params.len() == args.len() {
                                let map: std::collections::HashMap<&str, &Expr> =
                                    params.iter().map(|p| p.as_str()).zip(args.iter()).collect();
                                let mut expanded = crate::subst::subst_expr(body, &map);
                                expanded.span = span;
                                e = expanded;
                                continue;
                            }
                        }
                    }
                    e = Expr {
                        span,
                        kind: ExprKind::Call(Box::new(e), args),
                    };
                }
                T::Dot => {
                    self.bump();
                    let field = self.ident()?;
                    e = Expr {
                        span: e.span.to(field.span),
                        kind: ExprKind::Field(Box::new(e), field),
                    };
                }
                T::Lt
                    if self.ty_mode && matches!(e.kind, ExprKind::Var(_) | ExprKind::Field(..)) =>
                {
                    self.bump();
                    let args = self.with_mode(true, |p| p.comma_list(&T::Gt))?;
                    let end = self.expect(&T::Gt)?;
                    e = Expr {
                        span: e.span.to(end),
                        kind: ExprKind::TypeApp(Box::new(e), args),
                    };
                }
                _ => return Ok(e),
            }
        }
    }

    /// Comma-separated expressions up to (not including) `close`.
    fn comma_list(&mut self, close: &T) -> PResult<Vec<Expr>> {
        let mut out = Vec::new();
        while self.peek() != close {
            out.push(self.expr_bp(0)?);
            if !self.eat(&T::Comma) {
                break;
            }
        }
        Ok(out)
    }

    fn atom(&mut self) -> PResult<Expr> {
        let start = self.span();
        let kind = match self.peek().clone() {
            T::Nat(n) => {
                self.bump();
                ExprKind::Nat(n)
            }
            T::Str(s) => {
                self.bump();
                ExprKind::Str(s)
            }
            T::Underscore => {
                self.bump();
                ExprKind::Wild
            }
            T::Ident(name)
                if (name == "forall" || name == "exists")
                    && self
                        .toks
                        .get(self.pos + 1)
                        .is_some_and(|t| t.kind == T::LParen) =>
            {
                self.bump();
                self.expect(&T::LParen)?;
                let mut binders = Vec::new();
                while *self.peek() != T::RParen {
                    let n = self.ident()?;
                    self.expect(&T::Colon)?;
                    let ty = self.ty()?;
                    binders.push((n, ty));
                    if !self.eat(&T::Comma) {
                        break;
                    }
                }
                self.expect(&T::RParen)?;
                self.expect(&T::Arrow)?;
                let body = self.ty()?;
                if name == "exists" {
                    // `exists(x: A, y: B) -> P` is `Exists(|x: A| Exists(|y: B| P))`
                    let mut acc = body;
                    for (n, ty) in binders.into_iter().rev() {
                        let sp = n.span.to(acc.span);
                        let lamb = Expr {
                            kind: ExprKind::Lambda {
                                params: vec![LamParam {
                                    name: n,
                                    ty: Some(ty),
                                }],
                                body: Box::new(acc),
                            },
                            span: sp,
                        };
                        acc = Expr {
                            kind: ExprKind::Call(
                                Box::new(Expr {
                                    kind: ExprKind::Var("Exists".into()),
                                    span: sp,
                                }),
                                vec![lamb],
                            ),
                            span: sp,
                        };
                    }
                    return Ok(Expr {
                        kind: acc.kind,
                        span: start.to(acc.span),
                    });
                }
                ExprKind::Forall(binders, Box::new(body))
            }
            T::Ident(name) => {
                self.bump();
                ExprKind::Var(name)
            }
            T::LParen => {
                self.bump();
                if self.eat(&T::RParen) {
                    ExprKind::Unit
                } else {
                    let inner = self.expr()?;
                    let end = self.expect(&T::RParen)?;
                    return Ok(Expr {
                        kind: inner.kind,
                        span: start.to(end),
                    });
                }
            }
            T::LBrace => ExprKind::Block(self.block()?),
            T::Do => {
                self.bump();
                ExprKind::Do(self.block()?)
            }
            T::LBracket => {
                self.bump();
                let items = self.with_mode(false, |p| p.comma_list(&T::RBracket))?;
                self.expect(&T::RBracket)?;
                ExprKind::List(items)
            }
            T::For => {
                self.bump();
                let var = self.ident()?;
                self.expect(&T::In)?;
                let iter = self.expr()?;
                let body = self.block()?;
                ExprKind::For {
                    var,
                    iter: Box::new(iter),
                    body,
                }
            }
            T::If => {
                self.bump();
                let cond = self.expr()?;
                let then = self.block()?;
                let els = if self.eat(&T::Else) {
                    Some(Box::new(if *self.peek() == T::If {
                        self.atom()?
                    } else {
                        let b = self.block()?;
                        Expr {
                            span: b.span,
                            kind: ExprKind::Block(b),
                        }
                    }))
                } else {
                    None
                };
                ExprKind::If(Box::new(cond), then, els)
            }
            T::Match => {
                self.bump();
                let scrut = self.expr()?;
                self.expect(&T::LBrace)?;
                let mut arms = Vec::new();
                while *self.peek() != T::RBrace {
                    let pat = self.expr()?;
                    self.expect(&T::FatArrow)?;
                    let body = self.expr()?;
                    let sep = self.eat(&T::Comma);
                    if !sep && *self.peek() != T::RBrace && !is_block_like(&body) {
                        return self.err(format!(
                            "expected `,` or `}}` after match arm, found {}",
                            self.peek()
                        ));
                    }
                    arms.push(Arm { pat, body });
                }
                self.expect(&T::RBrace)?;
                ExprKind::Match(Box::new(scrut), arms)
            }
            other => return self.err(format!("expected expression, found {other}")),
        };
        Ok(Expr {
            kind,
            span: start.to(self.prev_span()),
        })
    }
}

/// A variable, a field of a place, or a dereference of one.
fn is_place(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Var(_) => true,
        ExprKind::Field(b, _) | ExprKind::Deref(b) => is_place(b),
        _ => false,
    }
}

fn is_block_like(e: &Expr) -> bool {
    matches!(
        e.kind,
        ExprKind::Block(_)
            | ExprKind::Do(_)
            | ExprKind::For { .. }
            | ExprKind::If(..)
            | ExprKind::Match(..)
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ok(src: &str) -> Module {
        parse(src).unwrap_or_else(|e| {
            panic!("{}", apex_span::render_diagnostic("t", src, &e.msg, e.span))
        })
    }

    fn err(src: &str) -> String {
        parse(src).unwrap_err().msg
    }

    fn only_fn(m: &Module) -> &FnDecl {
        match &m.items[0].kind {
            ItemKind::Fn(f) => f,
            _ => panic!("not a fn"),
        }
    }

    #[test]
    fn generic_return_type_vs_comparison() {
        let m = ok("fn f<T, n: Nat>(own v: Vec<T, n>) -> Vec<T, n + 1> { v }");
        let f = only_fn(&m);
        assert_eq!(f.generics.len(), 2);
        assert_eq!(f.params[0].mode, Mode::Own);
        assert!(matches!(
            f.ret.as_ref().unwrap().kind,
            ExprKind::TypeApp(..)
        ));
        let m = ok("fn g(a: Nat, b: Nat) -> Bool { a < b }");
        let tail = only_fn(&m).body.as_ref().unwrap().tail.as_ref().unwrap();
        assert!(matches!(tail.kind, ExprKind::Binary(BinOp::Lt, ..)));
    }

    #[test]
    fn precedence() {
        let m = ok("fn f() -> Nat { 1 + 2 * 3 }");
        let tail = only_fn(&m).body.as_ref().unwrap().tail.as_ref().unwrap();
        match &tail.kind {
            ExprKind::Binary(BinOp::Add, _, r) => {
                assert!(matches!(r.kind, ExprKind::Binary(BinOp::Mul, ..)))
            }
            k => panic!("{k:?}"),
        }
    }

    #[test]
    fn self_params_and_refs() {
        let m = ok("trait T { fn f(&mut self, x: &'a Nat) -> &'a Nat; }");
        let ItemKind::Trait(t) = &m.items[0].kind else {
            panic!()
        };
        assert!(t.fns[0].body.is_none());
        assert!(matches!(
            t.fns[0].params[0].ty.kind,
            ExprKind::Ref { mutable: true, .. }
        ));
    }

    fn tactics(src: &str) -> Vec<Tactic> {
        let toks = lex(src).unwrap();
        let toks = &toks[..toks.len() - 1]; // drop Eof
        parse_tactics(toks, Span::new(0, 0), &Notations::default()).unwrap()
    }

    #[test]
    fn tactic_syntax() {
        use TacticKind as K;
        let ts = tactics("intro a b; rw [h, <- g]\n simp [ih]\n exact foo(a)\n rfl");
        assert!(matches!(&ts[0].kind, K::Intro(v) if v.len() == 2));
        assert!(matches!(&ts[1].kind, K::Rw(r, None) if r.len() == 2 && !r[0].0 && r[1].0));
        assert!(matches!(&ts[2].kind, K::Simp(l, None) if l.len() == 1));
        assert!(matches!(&ts[3].kind, K::Exact(_)));
        assert!(matches!(&ts[4].kind, K::Rfl));
        let ts = tactics("induction n with { zero => { rfl }, succ(m, ih) => { simp [ih] } }");
        let K::Induction(v, _, Some(arms)) = &ts[0].kind else {
            panic!()
        };
        assert_eq!(v.name, "n");
        assert_eq!(arms.len(), 2);
        assert_eq!(arms[1].binders.len(), 2);
        let ts = tactics("have h: a = b := by { rfl }\n { exact h }");
        assert!(matches!(
            &ts[0].kind,
            K::Have {
                proof: HaveProof::Tactic(_),
                ..
            }
        ));
        assert!(matches!(&ts[1].kind, K::Block(_)));
    }

    #[test]
    fn tactic_errors() {
        let toks = lex("frobnicate").unwrap();
        let toks = &toks[..toks.len() - 1];
        let e = parse_tactics(toks, Span::new(0, 0), &Notations::default()).unwrap_err();
        assert!(e.msg.contains("expected a tactic"));
    }

    #[test]
    fn simp_attribute() {
        let m = ok("#[simp]\ntheorem t(a: Nat): a = a := rfl");
        let ItemKind::Theorem(t) = &m.items[0].kind else {
            panic!()
        };
        assert!(t.simp);
        assert!(parse("#[inline] theorem t(a: Nat): a = a := rfl").is_err());
        assert!(parse("#[simp] fn f() {}").is_err());
    }

    #[test]
    fn theorem_forms() {
        let m =
            ok("theorem t(a: Nat): a = a := by { simp { x } }\ntheorem u(a: Nat): a = a := rfl");
        let ItemKind::Theorem(t) = &m.items[0].kind else {
            panic!()
        };
        assert!(matches!(t.proof, Proof::Tactic(_)));
        let ItemKind::Theorem(u) = &m.items[1].kind else {
            panic!()
        };
        assert!(matches!(u.proof, Proof::Term(_)));
    }

    #[test]
    fn errors_are_located() {
        assert!(err("fn f() { 1 2 }").contains("expected `;` or `}`"));
        assert!(err("let x").contains("expected an item"));
        assert!(err("fn f( {").contains("expected identifier"));
        assert!(err("theorem t(): P := by { ").contains("unclosed"));
    }
}

#[cfg(test)]
mod loop_and_list_tests {
    use super::*;

    #[test]
    fn list_literals_for_loops_and_remainder() {
        let m =
            parse("fn f() -> Nat { let xs := [1, 2, 3]; for x in xs { print(x) } 7 % 2 }").unwrap();
        let ItemKind::Fn(f) = &m.items[0].kind else {
            panic!()
        };
        let body = f.body.as_ref().unwrap();
        assert!(
            matches!(&body.stmts[0], Stmt::Let { init, .. } if matches!(init.kind, ExprKind::List(ref v) if v.len() == 3))
        );
        // a `for` loop is block-like: no `;` needed before the next expression
        assert!(matches!(&body.stmts[1], Stmt::Expr(e) if matches!(e.kind, ExprKind::For { .. })));
        assert!(matches!(
            body.tail.as_ref().unwrap().kind,
            ExprKind::Binary(BinOp::Rem, ..)
        ));
        // `for` still works as the keyword in `impl Trait for Type`
        assert!(parse("impl Show for Nat { fn show(&self) -> String { \"n\" } }").is_ok());
        assert!(parse("fn f() { [] }").is_ok());
    }

    #[test]
    fn closures() {
        let m = parse("fn f() { let g := |x, y: Nat| x + y; let h := || 1; g }").unwrap();
        let ItemKind::Fn(f) = &m.items[0].kind else {
            panic!()
        };
        let body = f.body.as_ref().unwrap();
        let Stmt::Let { init, .. } = &body.stmts[0] else {
            panic!()
        };
        let ExprKind::Lambda { params, .. } = &init.kind else {
            panic!()
        };
        assert_eq!(params.len(), 2);
        assert!(params[0].ty.is_none() && params[1].ty.is_some());
        let Stmt::Let { init, .. } = &body.stmts[1] else {
            panic!()
        };
        assert!(matches!(&init.kind, ExprKind::Lambda { params, .. } if params.is_empty()));
    }
}

#[cfg(test)]
mod assignment_tests {
    use super::*;

    #[test]
    fn assignments_and_derefs() {
        let m = parse("fn f(p: &mut Nat) { let mut x := 1; x = 2; x += 3; *p = x; p.a.b -= 1; }")
            .unwrap();
        let ItemKind::Fn(f) = &m.items[0].kind else {
            panic!()
        };
        let st = &f.body.as_ref().unwrap().stmts;
        assert!(matches!(&st[0], Stmt::Let { mutable: true, .. }));
        assert!(
            matches!(&st[1], Stmt::Assign { op: None, target, .. } if matches!(target.kind, ExprKind::Var(_)))
        );
        assert!(matches!(
            &st[2],
            Stmt::Assign {
                op: Some(BinOp::Add),
                ..
            }
        ));
        assert!(
            matches!(&st[3], Stmt::Assign { target, .. } if matches!(target.kind, ExprKind::Deref(_)))
        );
        assert!(
            matches!(&st[4], Stmt::Assign { op: Some(BinOp::Sub), target, .. } if matches!(target.kind, ExprKind::Field(..)))
        );
    }

    #[test]
    fn equality_is_still_an_expression_outside_statements() {
        // a proposition is an ordinary expression
        assert!(parse("theorem t(): 1 = 1 := rfl").is_ok());
        // `=` after a non-place is not an assignment
        let m = parse("fn f() -> Nat { g(1) = 2; 3 }").unwrap();
        let ItemKind::Fn(f) = &m.items[0].kind else {
            panic!()
        };
        assert!(matches!(&f.body.as_ref().unwrap().stmts[0], Stmt::Expr(_)));
    }

    #[test]
    fn bad_assignment_target() {
        assert!(parse("fn f() { 1 += 2; }").is_err());
    }
}
