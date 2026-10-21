//! Substitution of expressions for variables: how a macro call is expanded.
//! It is purely syntactic (not hygienic): a name bound inside the template that
//! equals a macro parameter shadows nothing and is replaced too.

use crate::ast::*;
use std::collections::HashMap;

pub fn subst_expr(e: &Expr, map: &HashMap<&str, &Expr>) -> Expr {
    let go = |x: &Expr| subst_expr(x, map);
    let bx = |x: &Expr| Box::new(subst_expr(x, map));
    let kind = match &e.kind {
        ExprKind::Var(n) => match map.get(n.as_str()) {
            Some(r) => return (*r).clone(),
            None => ExprKind::Var(n.clone()),
        },
        ExprKind::Neg(a) => ExprKind::Neg(bx(a)),
        ExprKind::Ascribe(a, t) => ExprKind::Ascribe(bx(a), bx(t)),
        ExprKind::By(ts) => ExprKind::By(ts.clone()),
        ExprKind::Deref(a) => ExprKind::Deref(bx(a)),
        ExprKind::Binary(op, a, b) => ExprKind::Binary(*op, bx(a), bx(b)),
        ExprKind::Ref {
            mutable,
            lifetime,
            inner,
        } => ExprKind::Ref {
            mutable: *mutable,
            lifetime: lifetime.clone(),
            inner: bx(inner),
        },
        ExprKind::Arrow(a, b) => ExprKind::Arrow(bx(a), bx(b)),
        ExprKind::Forall(bs, body) => ExprKind::Forall(
            bs.iter().map(|(n, t)| (n.clone(), go(t))).collect(),
            bx(body),
        ),
        ExprKind::Call(f, args) => ExprKind::Call(bx(f), args.iter().map(go).collect()),
        ExprKind::TypeApp(f, args) => ExprKind::TypeApp(bx(f), args.iter().map(go).collect()),
        ExprKind::Field(b, f) => ExprKind::Field(bx(b), f.clone()),
        ExprKind::Block(b) => ExprKind::Block(subst_block(b, map)),
        ExprKind::Do(b) => ExprKind::Do(subst_block(b, map)),
        ExprKind::List(items) => ExprKind::List(items.iter().map(go).collect()),
        ExprKind::Lambda { params, body } => ExprKind::Lambda {
            params: params
                .iter()
                .map(|p| LamParam {
                    name: p.name.clone(),
                    ty: p.ty.as_ref().map(go),
                })
                .collect(),
            body: bx(body),
        },
        ExprKind::For { var, iter, body } => ExprKind::For {
            var: var.clone(),
            iter: bx(iter),
            body: subst_block(body, map),
        },
        ExprKind::If(c, t, e2) => ExprKind::If(
            bx(c),
            subst_block(t, map),
            e2.as_ref().map(|x| Box::new(subst_expr(x, map))),
        ),
        ExprKind::Match(s, arms) => ExprKind::Match(
            bx(s),
            arms.iter()
                .map(|a| Arm {
                    pat: a.pat.clone(),
                    body: go(&a.body),
                })
                .collect(),
        ),
        other => other.clone(),
    };
    Expr { kind, span: e.span }
}

fn subst_block(b: &Block, map: &HashMap<&str, &Expr>) -> Block {
    let go = |x: &Expr| subst_expr(x, map);
    Block {
        stmts: b
            .stmts
            .iter()
            .map(|s| match s {
                Stmt::Let {
                    mutable,
                    name,
                    ty,
                    init,
                } => Stmt::Let {
                    mutable: *mutable,
                    name: name.clone(),
                    ty: ty.as_ref().map(go),
                    init: go(init),
                },
                Stmt::Bind { name, ty, action } => Stmt::Bind {
                    name: name.clone(),
                    ty: ty.as_ref().map(go),
                    action: go(action),
                },
                Stmt::Assign { target, op, value } => Stmt::Assign {
                    target: go(target),
                    op: *op,
                    value: go(value),
                },
                Stmt::Expr(e) => Stmt::Expr(go(e)),
            })
            .collect(),
        tail: b.tail.as_ref().map(|t| Box::new(go(t))),
        span: b.span,
    }
}
