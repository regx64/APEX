//! A function's borrowing signature, with lifetime elision.

use apex_span::Span;
use apex_syntax::ast::*;

/// How a parameter receives its argument.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParamKind {
    /// An ordinary parameter (copied).
    Value,
    /// `own x: T`: a linear value, moved in.
    Own,
    /// `&T`
    Ref,
    /// `&mut T`
    RefMut,
}

/// What the returned value may borrow from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RetKind {
    Value,
    /// The result is a reference derived from these parameters (indices into `params`).
    Ref(Vec<usize>),
}

/// The borrowing signature of a function (explicit parameters only, `self` first).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Callee {
    pub params: Vec<ParamKind>,
    pub ret: RetKind,
    /// Whether the declared return type is `IO<..>`.
    pub returns_io: bool,
}

impl Callee {
    pub fn has_mut_params(&self) -> bool {
        self.params.contains(&ParamKind::RefMut)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SigError {
    pub msg: String,
    pub span: Span,
}

fn err<X>(span: Span, msg: impl Into<String>) -> Result<X, SigError> {
    Err(SigError {
        msg: msg.into(),
        span,
    })
}

pub fn param_kind(p: &Param) -> ParamKind {
    match &p.ty.kind {
        ExprKind::Ref { mutable: true, .. } => ParamKind::RefMut,
        ExprKind::Ref { mutable: false, .. } => ParamKind::Ref,
        _ if p.mode == Mode::Own => ParamKind::Own,
        _ => ParamKind::Value,
    }
}

/// Every reference in a type expression, as (is mutable, lifetime name).
fn refs_in(e: &Expr, out: &mut Vec<(bool, Option<String>)>) {
    match &e.kind {
        ExprKind::Ref {
            mutable,
            lifetime,
            inner,
        } => {
            out.push((*mutable, lifetime.clone()));
            refs_in(inner, out);
        }
        ExprKind::TypeApp(f, args) | ExprKind::Call(f, args) => {
            refs_in(f, out);
            args.iter().for_each(|a| refs_in(a, out));
        }
        ExprKind::Arrow(a, b) => {
            refs_in(a, out);
            refs_in(b, out);
        }
        _ => {}
    }
}

fn is_io(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::TypeApp(f, _) | ExprKind::Call(f, _) => {
            matches!(&f.kind, ExprKind::Var(n) if n == "IO")
        }
        _ => false,
    }
}

/// The borrowing signature of `f`. `outer` lists lifetimes declared by the
/// enclosing impl or trait. Applies Rust's elision rules to a returned reference.
pub fn callee_of(f: &FnDecl, outer: &[String]) -> Result<Callee, SigError> {
    let params: Vec<ParamKind> = f.params.iter().map(param_kind).collect();
    let returns_io = f.ret.as_ref().is_some_and(is_io);
    let mut ret_refs = Vec::new();
    if let Some(r) = &f.ret {
        refs_in(r, &mut ret_refs);
    }
    if returns_io && params.contains(&ParamKind::RefMut) {
        return err(
            f.name.span,
            "a function with `&mut` parameters cannot return `IO` yet: the updated values would depend on running the action",
        );
    }
    if ret_refs.is_empty() {
        return Ok(Callee {
            params,
            ret: RetKind::Value,
            returns_io,
        });
    }
    if ret_refs.iter().any(|(m, _)| *m) {
        return err(
            f.ret.as_ref().map_or(f.name.span, |r| r.span),
            "returning `&mut` is not supported yet; return the updated value instead",
        );
    }
    let declared: Vec<&str> = f
        .generics
        .iter()
        .map(|g| g.name.name.as_str())
        .chain(outer.iter().map(String::as_str))
        .collect();
    let mut sources: Vec<usize> = Vec::new();
    for (_, lt) in &ret_refs {
        match lt {
            Some(name) if name == "'static" => {}
            Some(name) => {
                if !declared.contains(&name.as_str()) {
                    return err(
                        f.name.span,
                        format!("use of undeclared lifetime name `{name}` (declare it: `fn {}<{name}>`)", f.name.name),
                    );
                }
                let mut found = false;
                for (i, p) in f.params.iter().enumerate() {
                    let mut refs = Vec::new();
                    refs_in(&p.ty, &mut refs);
                    if refs
                        .iter()
                        .any(|(_, l)| l.as_deref() == Some(name.as_str()))
                    {
                        found = true;
                        if !sources.contains(&i) {
                            sources.push(i);
                        }
                    }
                }
                if !found {
                    return err(
                        f.name.span,
                        format!(
                            "the returned reference has lifetime `{name}`, but no parameter does"
                        ),
                    );
                }
            }
            None => {
                // elided: `&self`, else the only borrowed parameter
                let borrowed: Vec<usize> = (0..params.len())
                    .filter(|&i| matches!(params[i], ParamKind::Ref | ParamKind::RefMut))
                    .collect();
                let self_idx = f.params.iter().position(|p| p.name.name == "self");
                let pick = match (self_idx, borrowed.as_slice()) {
                    (Some(i), _) if borrowed.contains(&i) => Some(i),
                    (_, [only]) => Some(*only),
                    _ => None,
                };
                match pick {
                    Some(i) => {
                        if !sources.contains(&i) {
                            sources.push(i);
                        }
                    }
                    None => {
                        let why = if borrowed.is_empty() {
                            "there is no borrowed parameter to take it from".to_string()
                        } else {
                            format!(
                                "there are {} borrowed parameters, so it could come from any of them (name a lifetime: `&'a T` on the result and on one parameter)",
                                borrowed.len()
                            )
                        };
                        return err(
                            f.ret.as_ref().map_or(f.name.span, |r| r.span),
                            format!("missing lifetime specifier: the returned reference has no lifetime, and {why}"),
                        );
                    }
                }
            }
        }
    }
    sources.sort_unstable();
    Ok(Callee {
        params,
        ret: RetKind::Ref(sources),
        returns_io,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use apex_syntax::parse;

    fn sig(src: &str) -> Result<Callee, SigError> {
        let m = parse(src).unwrap();
        let ItemKind::Fn(f) = &m.items[0].kind else {
            panic!()
        };
        callee_of(f, &[])
    }

    #[test]
    fn kinds_and_plain_return() {
        let c = sig("fn f(a: Nat, own b: Nat, c: &Nat, d: &mut Nat) -> Nat { a }").unwrap();
        assert_eq!(
            c.params,
            vec![
                ParamKind::Value,
                ParamKind::Own,
                ParamKind::Ref,
                ParamKind::RefMut
            ]
        );
        assert_eq!(c.ret, RetKind::Value);
    }

    #[test]
    fn elision_picks_the_only_borrowed_parameter() {
        let c = sig("fn first(n: Nat, v: &List<Nat>) -> &Nat { n }").unwrap();
        assert_eq!(c.ret, RetKind::Ref(vec![1]));
    }

    #[test]
    fn self_wins_over_other_borrows() {
        let c = sig("fn get(&self, other: &Nat) -> &Nat { other }").unwrap();
        assert_eq!(c.ret, RetKind::Ref(vec![0]));
    }

    #[test]
    fn two_borrowed_parameters_need_a_lifetime() {
        let e = sig("fn pick(a: &Nat, b: &Nat) -> &Nat { a }").unwrap_err();
        assert!(e.msg.contains("missing lifetime specifier"), "{}", e.msg);
        assert!(e.msg.contains("2 borrowed parameters"), "{}", e.msg);
        // naming the lifetime resolves it
        let c = sig("fn pick<'a>(a: &'a Nat, b: &Nat) -> &'a Nat { a }").unwrap();
        assert_eq!(c.ret, RetKind::Ref(vec![0]));
    }

    #[test]
    fn no_borrowed_parameter_cannot_return_a_reference() {
        let e = sig("fn make(n: Nat) -> &Nat { n }").unwrap_err();
        assert!(e.msg.contains("no borrowed parameter"), "{}", e.msg);
    }

    #[test]
    fn undeclared_and_unused_lifetimes() {
        assert!(sig("fn f(a: &'a Nat) -> &'a Nat { a }")
            .unwrap_err()
            .msg
            .contains("undeclared lifetime"));
        assert!(sig("fn f<'a>(a: &Nat) -> &'a Nat { a }")
            .unwrap_err()
            .msg
            .contains("no parameter does"));
    }

    #[test]
    fn unsupported_shapes_are_reported() {
        assert!(sig("fn f(a: &mut Nat) -> &mut Nat { a }")
            .unwrap_err()
            .msg
            .contains("returning `&mut`"));
        assert!(sig("fn f(a: &mut Nat) -> IO<Unit> { a }")
            .unwrap_err()
            .msg
            .contains("cannot return `IO`"));
    }
}
