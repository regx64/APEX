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
    }
    .module()
}

struct Parser {
    toks: Vec<Token>,
    pos: usize,
    ty_mode: bool,
}

enum Infix {
    Arrow,
    Bin(BinOp),
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
        Ok(Module { items })
    }

    fn item(&mut self) -> PResult<Item> {
        let start = self.span();
        let kind = match self.peek() {
            T::Fn => ItemKind::Fn(self.fn_decl()?),
            T::Struct => ItemKind::Struct(self.struct_decl()?),
            T::Enum => ItemKind::Enum(self.enum_decl()?),
            T::Trait => ItemKind::Trait(self.trait_decl()?),
            T::Impl => ItemKind::Impl(self.impl_decl()?),
            T::Theorem => ItemKind::Theorem(self.theorem_decl()?),
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
        })
    }

    fn struct_decl(&mut self) -> PResult<StructDecl> {
        self.expect(&T::Struct)?;
        let name = self.ident()?;
        let generics = self.generics()?;
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
            fields,
        })
    }

    fn enum_decl(&mut self) -> PResult<EnumDecl> {
        self.expect(&T::Enum)?;
        let name = self.ident()?;
        let generics = self.generics()?;
        self.expect(&T::LBrace)?;
        let mut variants = Vec::new();
        while *self.peek() != T::RBrace {
            let vname = self.ident()?;
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
            variants.push(Variant {
                name: vname,
                fields,
            });
            if !self.eat(&T::Comma) {
                break;
            }
        }
        self.expect(&T::RBrace)?;
        Ok(EnumDecl {
            name,
            generics,
            variants,
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
        let stmt = self.expr()?;
        self.expect(&T::ColonEq)?;
        let proof = if self.eat(&T::By) {
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
            Proof::Tactic(toks)
        } else {
            Proof::Term(self.expr()?)
        };
        Ok(TheoremDecl {
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
            T::Arrow => (2, 1, Infix::Arrow),
            T::Eq => (4, 5, Infix::Bin(BinOp::Eq)),
            T::EqEq => (4, 5, Infix::Bin(BinOp::EqEq)),
            T::Lt if !self.ty_mode => (4, 5, Infix::Bin(BinOp::Lt)),
            T::Gt if !self.ty_mode => (4, 5, Infix::Bin(BinOp::Gt)),
            T::Plus => (6, 7, Infix::Bin(BinOp::Add)),
            T::Minus => (6, 7, Infix::Bin(BinOp::Sub)),
            T::Star => (8, 9, Infix::Bin(BinOp::Mul)),
            T::Slash => (8, 9, Infix::Bin(BinOp::Div)),
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
            };
            lhs = Expr { kind, span };
        }
        Ok(lhs)
    }

    fn prefix(&mut self) -> PResult<Expr> {
        let start = self.span();
        match self.peek() {
            T::Minus => {
                self.bump();
                let inner = self.expr_bp(10)?;
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
                let inner = self.expr_bp(10)?;
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
                    e = Expr {
                        span: e.span.to(end),
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

fn is_block_like(e: &Expr) -> bool {
    matches!(
        e.kind,
        ExprKind::Block(_) | ExprKind::If(..) | ExprKind::Match(..)
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
