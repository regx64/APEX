//! `#[derive(BEq, Show, Ord)]` and `struct B extends A { .. }`.
//!
//! Both are source-level conveniences: `derive` writes the `impl` a person would have
//! written and elaborates it like any other item, so the result is ordinary code that
//! the kernel checks (and whose errors, if any, are reported against the declaration).
//! `extends` copies the parent's fields in front of the new ones and adds `toA`.

use super::*;

fn real_generics(gs: &[Generic]) -> Vec<&Generic> {
    gs.iter()
        .filter(|g| !g.name.name.starts_with('\''))
        .collect()
}

fn subst_vars(e: &Expr, map: &HashMap<String, Expr>) -> Expr {
    let go = |x: &Expr| subst_vars(x, map);
    let kind = match &e.kind {
        ExprKind::Var(n) => match map.get(n) {
            Some(r) => return r.clone(),
            None => ExprKind::Var(n.clone()),
        },
        ExprKind::Arrow(a, b) => ExprKind::Arrow(Box::new(go(a)), Box::new(go(b))),
        ExprKind::TypeApp(f, args) => {
            ExprKind::TypeApp(Box::new(go(f)), args.iter().map(go).collect())
        }
        ExprKind::Call(f, args) => ExprKind::Call(Box::new(go(f)), args.iter().map(go).collect()),
        ExprKind::Ref {
            mutable,
            lifetime,
            inner,
        } => ExprKind::Ref {
            mutable: *mutable,
            lifetime: lifetime.clone(),
            inner: Box::new(go(inner)),
        },
        other => other.clone(),
    };
    Expr { kind, span: e.span }
}

/// `if a { if b { c } else { false } } else { false }`
fn and_chain(conds: &[String]) -> String {
    match conds {
        [] => "true".into(),
        [c] => c.clone(),
        [c, rest @ ..] => format!("if {c} {{ {} }} else {{ false }}", and_chain(rest)),
    }
}

/// `String.append(p1, String.append(p2, ..))` for literal and computed parts.
enum Part {
    Lit(String),
    Code(String),
}

fn concat(parts: Vec<Part>) -> String {
    let render = |p: &Part| match p {
        Part::Lit(s) => format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\"")),
        Part::Code(c) => c.clone(),
    };
    let mut it = parts.iter().rev();
    let Some(last) = it.next() else {
        return "\"\"".into();
    };
    it.fold(render(last), |acc, p| {
        format!("String.append({}, {acc})", render(p))
    })
}

fn names(prefix: &str, n: usize) -> Vec<String> {
    (0..n).map(|i| format!("{prefix}{i}")).collect()
}

impl Elaborator {
    pub(super) fn elab_struct_item(&mut self, s: &StructDecl, span: Span) -> R<()> {
        let flat = self.flatten_struct(s)?;
        self.elab_struct(&flat, span)?;
        self.tables
            .struct_decls
            .insert(flat.name.name.clone(), flat.clone());
        if let Some(p) = &s.parent {
            self.gen_to_parent(&flat, p, span)?;
        }
        let fields: Vec<String> = flat.fields.iter().map(|f| f.name.name.clone()).collect();
        for tr in &flat.derives {
            let text = self.derive_text(
                tr,
                &flat.name.name,
                &flat.generics,
                Shape::Struct(&fields),
                span,
            )?;
            self.elab_generated(&text, tr, &flat.name.name, span)?;
        }
        Ok(())
    }

    pub(super) fn elab_enum_item(&mut self, e: &EnumDecl, span: Span) -> R<()> {
        self.elab_enum(e, span)?;
        let variants: Vec<(String, usize)> = e
            .variants
            .iter()
            .map(|v| (v.name.name.clone(), v.fields.len()))
            .collect();
        // fields of the enum's own type: the derived functions recurse on them
        let recs: Vec<Vec<bool>> = e
            .variants
            .iter()
            .map(|v| {
                v.fields
                    .iter()
                    .map(|f| mentions_expr(f, &e.name.name))
                    .collect()
            })
            .collect();
        for tr in &e.derives {
            let text = self.derive_text(
                tr,
                &e.name.name,
                &e.generics,
                Shape::Enum(&variants, &recs),
                span,
            )?;
            self.elab_generated(&text, tr, &e.name.name, span)?;
        }
        Ok(())
    }

    fn elab_generated(&mut self, text: &str, tr: &str, ty: &str, span: Span) -> R<()> {
        let module = apex_syntax::parse(text).map_err(|e| {
            ElabError::new(span, format!("cannot derive `{tr}` for `{ty}`: {}", e.msg))
        })?;
        for item in &module.items {
            self.elab_item(item).map_err(|mut e| {
                e.msg = format!("cannot derive `{tr}` for `{ty}`: {}", e.msg);
                e.span = span;
                e
            })?;
        }
        Ok(())
    }

    fn flatten_struct(&self, s: &StructDecl) -> R<StructDecl> {
        let Some(pe) = &s.parent else {
            return Ok(s.clone());
        };
        let (pname, pargs): (String, Vec<Expr>) = match &pe.kind {
            ExprKind::Var(n) => (n.clone(), vec![]),
            ExprKind::TypeApp(f, args) | ExprKind::Call(f, args) => match &f.kind {
                ExprKind::Var(n) => (n.clone(), args.clone()),
                _ => return err(pe.span, "a parent must be a struct name"),
            },
            _ => return err(pe.span, "a parent must be a struct name"),
        };
        let Some(pdecl) = self.tables.struct_decls.get(&pname) else {
            return err(pe.span, format!("unknown parent struct `{pname}`"));
        };
        let gens = real_generics(&pdecl.generics);
        if gens.len() != pargs.len() {
            return err(
                pe.span,
                format!(
                    "`{pname}` takes {} type arguments, found {}",
                    gens.len(),
                    pargs.len()
                ),
            );
        }
        let map: HashMap<String, Expr> = gens
            .iter()
            .zip(&pargs)
            .map(|(g, a)| (g.name.name.clone(), a.clone()))
            .collect();
        let mut fields: Vec<Field> = pdecl
            .fields
            .iter()
            .map(|f| Field {
                name: f.name.clone(),
                ty: subst_vars(&f.ty, &map),
            })
            .collect();
        for f in &s.fields {
            if fields.iter().any(|g| g.name.name == f.name.name) {
                return err(
                    f.name.span,
                    format!(
                        "field `{}` is already inherited from `{pname}`",
                        f.name.name
                    ),
                );
            }
        }
        fields.extend(s.fields.iter().cloned());
        Ok(StructDecl {
            parent: None,
            fields,
            ..s.clone()
        })
    }

    /// `impl B { fn toA(self) -> A { A.mk(self.x, ..) } }` for non-generic parents.
    fn gen_to_parent(&mut self, child: &StructDecl, parent: &Expr, span: Span) -> R<()> {
        let ExprKind::Var(pname) = &parent.kind else {
            return Ok(());
        };
        let Some(pdecl) = self.tables.struct_decls.get(pname).cloned() else {
            return Ok(());
        };
        if !child.generics.is_empty() || !pdecl.generics.is_empty() {
            return Ok(());
        }
        let args: Vec<String> = pdecl
            .fields
            .iter()
            .map(|f| format!("self.{}", f.name.name))
            .collect();
        let text = format!(
            "impl {c} {{ fn to{p}(self) -> {p} {{ {p}.mk({}) }} }}",
            args.join(", "),
            c = child.name.name,
            p = pname
        );
        self.elab_generated(&text, "extends", &child.name.name, span)
    }

    fn derive_text(
        &self,
        tr: &str,
        name: &str,
        generics: &[Generic],
        shape: Shape<'_>,
        span: Span,
    ) -> R<String> {
        let gs = real_generics(generics);
        let (header, self_ty) = if gs.is_empty() {
            (format!("impl {tr} for {name}"), name.to_string())
        } else {
            let params: Vec<String> = gs
                .iter()
                .map(|g| format!("{}: {tr}", g.name.name))
                .collect();
            let args: Vec<String> = gs.iter().map(|g| g.name.name.clone()).collect();
            (
                format!(
                    "impl<{}> {tr} for {name}<{}>",
                    params.join(", "),
                    args.join(", ")
                ),
                format!("{name}<{}>", args.join(", ")),
            )
        };
        let recursive = matches!(&shape, Shape::Enum(_, recs) if recs.iter().flatten().any(|r| *r));
        if recursive {
            return self.derive_recursive(tr, name, &gs, &shape, &header, span);
        }
        let _ = self_ty;
        let body = match (tr, &shape) {
            ("BEq", Shape::Struct(fields)) => {
                let conds: Vec<String> = fields
                    .iter()
                    .map(|f| format!("self.{f} == other.{f}"))
                    .collect();
                format!(
                    "fn beq(self, other: Self) -> Bool {{ {} }}",
                    and_chain(&conds)
                )
            }
            ("BEq", Shape::Enum(vs, _)) => {
                let arms: Vec<String> = vs
                    .iter()
                    .map(|(v, n)| {
                        let (a, b) = (names("a", *n), names("b", *n));
                        let conds: Vec<String> = a
                            .iter()
                            .zip(&b)
                            .map(|(x, y)| format!("{x} == {y}"))
                            .collect();
                        format!(
                            "{name}.{v}{pa} => match other {{ {name}.{v}{pb} => {}, _ => false }}",
                            and_chain(&conds),
                            pa = pat_args(&a),
                            pb = pat_args(&b)
                        )
                    })
                    .collect();
                format!(
                    "fn beq(self, other: Self) -> Bool {{ match self {{ {} }} }}",
                    arms.join(", ")
                )
            }
            ("Show", Shape::Struct(fields)) => {
                let mut parts = vec![Part::Lit(format!("{name} {{ "))];
                for (i, f) in fields.iter().enumerate() {
                    if i > 0 {
                        parts.push(Part::Lit(", ".into()));
                    }
                    parts.push(Part::Lit(format!("{f}: ")));
                    parts.push(Part::Code(format!("self.{f}.show()")));
                }
                parts.push(Part::Lit(" }".into()));
                if fields.is_empty() {
                    parts = vec![Part::Lit(name.to_string())];
                }
                format!("fn show(&self) -> String {{ {} }}", concat(parts))
            }
            ("Show", Shape::Enum(vs, _)) => {
                let arms: Vec<String> = vs
                    .iter()
                    .map(|(v, n)| {
                        let a = names("a", *n);
                        let mut parts =
                            vec![Part::Lit(if *n == 0 { v.clone() } else { format!("{v}(") })];
                        for (i, x) in a.iter().enumerate() {
                            if i > 0 {
                                parts.push(Part::Lit(", ".into()));
                            }
                            parts.push(Part::Code(format!("{x}.show()")));
                        }
                        if *n > 0 {
                            parts.push(Part::Lit(")".into()));
                        }
                        format!("{name}.{v}{} => {}", pat_args(&a), concat(parts))
                    })
                    .collect();
                format!(
                    "fn show(&self) -> String {{ match self {{ {} }} }}",
                    arms.join(", ")
                )
            }
            ("Ord", Shape::Struct(fields)) => {
                fn lex(fields: &[String]) -> String {
                    match fields {
                        [] => "false".into(),
                        [f] => format!("self.{f} < other.{f}"),
                        [f, rest @ ..] => format!(
                            "if self.{f} < other.{f} {{ true }} else {{ if other.{f} < self.{f} {{ false }} else {{ {} }} }}",
                            lex(rest)
                        ),
                    }
                }
                format!("fn lt(self, other: Self) -> Bool {{ {} }}", lex(fields))
            }
            ("Ord", Shape::Enum(vs, _)) => {
                fn lex_vars(a: &[String], b: &[String]) -> String {
                    match (a, b) {
                        ([x], [y]) => format!("{x} < {y}"),
                        ([x, ra @ ..], [y, rb @ ..]) => format!(
                            "if {x} < {y} {{ true }} else {{ if {y} < {x} {{ false }} else {{ {} }} }}",
                            lex_vars(ra, rb)
                        ),
                        _ => "false".into(),
                    }
                }
                let arms: Vec<String> = vs
                    .iter()
                    .enumerate()
                    .map(|(i, (v, n))| {
                        let (a, b) = (names("a", *n), names("b", *n));
                        let inner: Vec<String> = vs
                            .iter()
                            .enumerate()
                            .map(|(j, (w, m))| {
                                let pb = pat_args(&names("b", *m));
                                let result = if j < i {
                                    "false".to_string()
                                } else if j > i {
                                    "true".to_string()
                                } else if *n == 0 {
                                    "false".to_string()
                                } else {
                                    lex_vars(&a, &b)
                                };
                                format!("{name}.{w}{pb} => {result}")
                            })
                            .collect();
                        format!(
                            "{name}.{v}{} => match other {{ {} }}",
                            pat_args(&a),
                            inner.join(", ")
                        )
                    })
                    .collect();
                format!(
                    "fn lt(self, other: Self) -> Bool {{ match self {{ {} }} }}",
                    arms.join(", ")
                )
            }
            _ => {
                return err(
                    span,
                    format!("cannot derive `{tr}` (supported: BEq, Show, Ord)"),
                )
            }
        };
        Ok(format!("{header} {{ {body} }}"))
    }
}

impl Elaborator {
    /// BEq / Show / Ord of an enum with fields of its own type: the recursion lives in a
    /// helper function (an `impl` method cannot call itself), which the `impl` delegates to.
    fn derive_recursive(
        &self,
        tr: &str,
        name: &str,
        gs: &[&Generic],
        shape: &Shape<'_>,
        header: &str,
        span: Span,
    ) -> R<String> {
        let Shape::Enum(vs, recs) = shape else {
            unreachable!("only enums are recursive")
        };
        let helper = format!("{name}_derived_{}", tr.to_lowercase());
        let gen_args: Vec<String> = gs.iter().map(|g| g.name.name.clone()).collect();
        let gen_decl: Vec<String> = gen_args.iter().map(|g| format!("{g}: {tr}")).collect();
        let (ty, gdecl) = if gs.is_empty() {
            (name.to_string(), String::new())
        } else {
            (
                format!("{name}<{}>", gen_args.join(", ")),
                format!("<{}>", gen_decl.join(", ")),
            )
        };
        match tr {
            "BEq" => {
                let arms: Vec<String> = vs
                    .iter()
                    .zip(recs.iter())
                    .map(|((v, n), rs)| {
                        let (a, b) = (names("a", *n), names("b", *n));
                        let conds: Vec<String> = (0..*n)
                            .map(|i| {
                                if rs[i] {
                                    format!("{helper}({}, {})", a[i], b[i])
                                } else {
                                    format!("{} == {}", a[i], b[i])
                                }
                            })
                            .collect();
                        format!(
                            "{name}.{v}{pa} => match y {{ {name}.{v}{pb} => {}, _ => false }}",
                            and_chain(&conds),
                            pa = pat_args(&a),
                            pb = pat_args(&b)
                        )
                    })
                    .collect();
                Ok(format!(
                    "fn {helper}{gdecl}(x: {ty}, y: {ty}) -> Bool {{ match x {{ {} }} }}\n\
                     {header} {{ fn beq(self, other: Self) -> Bool {{ {helper}(self, other) }} }}",
                    arms.join(", ")
                ))
            }
            "Show" => {
                let arms: Vec<String> = vs
                    .iter()
                    .zip(recs.iter())
                    .map(|((v, n), rs)| {
                        let a = names("a", *n);
                        let mut parts =
                            vec![Part::Lit(if *n == 0 { v.clone() } else { format!("{v}(") })];
                        for (i, x) in a.iter().enumerate() {
                            if i > 0 {
                                parts.push(Part::Lit(", ".into()));
                            }
                            parts.push(Part::Code(if rs[i] {
                                format!("{helper}({x})")
                            } else {
                                format!("{x}.show()")
                            }));
                        }
                        if *n > 0 {
                            parts.push(Part::Lit(")".into()));
                        }
                        format!("{name}.{v}{} => {}", pat_args(&a), concat(parts))
                    })
                    .collect();
                Ok(format!(
                    "fn {helper}{gdecl}(x: {ty}) -> String {{ match x {{ {} }} }}\n\
                     {header} {{ fn show(&self) -> String {{ {helper}(self) }} }}",
                    arms.join(", ")
                ))
            }
            "Ord" => {
                // a three-way comparison (0 less, 1 equal, 2 greater) returned by the helper:
                // recursion only ever goes forward on the first argument
                let cmp_of = |x: &str, y: &str, rec: bool| {
                    if rec {
                        format!("{helper}({x}, {y})")
                    } else {
                        format!("if {x} < {y} {{ 0 }} else {{ if {y} < {x} {{ 2 }} else {{ 1 }} }}")
                    }
                };
                fn lex(
                    a: &[String],
                    b: &[String],
                    rs: &[bool],
                    cmp_of: &dyn Fn(&str, &str, bool) -> String,
                ) -> String {
                    match (a, b, rs) {
                        ([x], [y], [r]) => cmp_of(x, y, *r),
                        ([x, ra @ ..], [y, rb @ ..], [r, rr @ ..]) => {
                            let c = cmp_of(x, y, *r);
                            format!(
                                "if ({c}) == 1 {{ {} }} else {{ {c} }}",
                                lex(ra, rb, rr, cmp_of)
                            )
                        }
                        _ => "1".into(),
                    }
                }
                let arms: Vec<String> = vs
                    .iter()
                    .zip(recs.iter())
                    .enumerate()
                    .map(|(i, ((v, n), rs))| {
                        let (a, b) = (names("a", *n), names("b", *n));
                        let inner: Vec<String> = vs
                            .iter()
                            .enumerate()
                            .map(|(j, (w, m))| {
                                let pb = pat_args(&names("b", *m));
                                let result = if j < i {
                                    "2".to_string()
                                } else if j > i {
                                    "0".to_string()
                                } else if *n == 0 {
                                    "1".to_string()
                                } else {
                                    lex(&a, &b, rs, &cmp_of)
                                };
                                format!("{name}.{w}{pb} => {result}")
                            })
                            .collect();
                        format!(
                            "{name}.{v}{} => match y {{ {} }}",
                            pat_args(&a),
                            inner.join(", ")
                        )
                    })
                    .collect();
                Ok(format!(
                    "fn {helper}{gdecl}(x: {ty}, y: {ty}) -> Nat {{ match x {{ {} }} }}\n\
                     {header} {{ fn lt(self, other: Self) -> Bool {{ {helper}(self, other) == 0 }} }}",
                    arms.join(", ")
                ))
            }
            _ => err(
                span,
                format!("cannot derive `{tr}` (supported: BEq, Show, Ord)"),
            ),
        }
    }
}

fn pat_args(names: &[String]) -> String {
    if names.is_empty() {
        String::new()
    } else {
        format!("({})", names.join(", "))
    }
}

enum Shape<'a> {
    Struct(&'a [String]),
    Enum(&'a [(String, usize)], &'a [Vec<bool>]),
}
