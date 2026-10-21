//! `apex doc`: Markdown documentation from signatures and `///` comments.

use apex_syntax::ast::{Item, ItemKind};

/// The `///` lines directly above byte offset `at`.
fn doc_comment(src: &str, at: usize) -> String {
    let before = &src[..at];
    let mut lines: Vec<&str> = Vec::new();
    for l in before
        .lines()
        .rev()
        .skip(if before.ends_with('\n') { 0 } else { 1 })
    {
        let t = l.trim();
        if let Some(rest) = t.strip_prefix("///") {
            lines.push(rest.strip_prefix(' ').unwrap_or(rest));
        } else if t.starts_with("#[") {
            continue;
        } else {
            break;
        }
    }
    lines.reverse();
    lines.join("\n")
}

/// The declaration up to its body (`{` or `:=`) at nesting depth 0.
fn signature(src: &str, item: &Item) -> String {
    let text = &src[item.span.start as usize..item.span.end as usize];
    let (mut depth, mut end) = (0i32, text.len());
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            b'{' if depth == 0 => {
                end = i;
                break;
            }
            b':' if depth == 0 && bytes.get(i + 1) == Some(&b'=') => {
                end = i;
                break;
            }
            _ => {}
        }
        i += 1;
    }
    text[..end].split_whitespace().collect::<Vec<_>>().join(" ")
}

fn render(src: &str, items: &[Item], prefix: &str, out: &mut String) {
    for item in items {
        let (kind, name) = match &item.kind {
            ItemKind::Fn(f) => ("fn", f.name.name.clone()),
            ItemKind::Theorem(t) => ("theorem", t.name.name.clone()),
            ItemKind::Struct(s) => ("struct", s.name.name.clone()),
            ItemKind::Enum(e) => ("enum", e.name.name.clone()),
            ItemKind::Trait(t) => ("trait", t.name.name.clone()),
            ItemKind::Impl(_) => ("impl", String::new()),
            ItemKind::Namespace { name, items } => {
                let p = format!("{prefix}{name}.");
                out.push_str(&format!("## namespace `{prefix}{name}`\n\n"));
                let doc = doc_comment(src, item.span.start as usize);
                if !doc.is_empty() {
                    out.push_str(&format!("{doc}\n\n"));
                }
                render(src, items, &p, out);
                continue;
            }
            ItemKind::Section(items) => {
                render(src, items, prefix, out);
                continue;
            }
            _ => continue,
        };
        let title = if name.is_empty() {
            "impl".to_string()
        } else {
            format!("{kind} {prefix}{name}")
        };
        out.push_str(&format!(
            "### {title}\n\n```apex\n{}\n```\n\n",
            signature(src, item)
        ));
        let doc = doc_comment(src, item.span.start as usize);
        if !doc.is_empty() {
            out.push_str(&format!("{doc}\n\n"));
        }
    }
}

pub fn generate(title: &str, src: &str) -> Result<String, String> {
    let module = apex_syntax::parse(src).map_err(|e| e.msg)?;
    let mut out = format!("# {title}\n\n");
    render(src, &module.items, "", &mut out);
    Ok(out)
}
