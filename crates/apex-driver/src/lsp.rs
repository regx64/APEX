//! `apex lsp`: a small language server over stdio.
//!
//! It keeps the text of open documents and answers with diagnostics from the real checker
//! (parse and elaboration errors, with their positions) on open, change and save. It also
//! answers `initialize`/`shutdown`. No completion or hover yet.

use std::collections::HashMap;
use std::io::{BufRead, Write};

// ---- a tiny JSON ----

#[derive(Clone, Debug, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    Num(f64),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
}

impl Json {
    pub fn get(&self, k: &str) -> Option<&Json> {
        match self {
            Json::Obj(kv) => kv.iter().find(|(n, _)| n == k).map(|(_, v)| v),
            _ => None,
        }
    }
    pub fn str(&self) -> Option<&str> {
        match self {
            Json::Str(s) => Some(s),
            _ => None,
        }
    }
    pub fn render(&self) -> String {
        match self {
            Json::Null => "null".into(),
            Json::Bool(b) => b.to_string(),
            Json::Num(n) => {
                if n.fract() == 0.0 {
                    format!("{}", *n as i64)
                } else {
                    n.to_string()
                }
            }
            Json::Str(s) => {
                let mut o = String::from("\"");
                for c in s.chars() {
                    match c {
                        '"' => o.push_str("\\\""),
                        '\\' => o.push_str("\\\\"),
                        '\n' => o.push_str("\\n"),
                        '\r' => o.push_str("\\r"),
                        '\t' => o.push_str("\\t"),
                        c if (c as u32) < 0x20 => o.push_str(&format!("\\u{:04x}", c as u32)),
                        c => o.push(c),
                    }
                }
                o.push('"');
                o
            }
            Json::Arr(a) => format!(
                "[{}]",
                a.iter().map(Json::render).collect::<Vec<_>>().join(",")
            ),
            Json::Obj(kv) => format!(
                "{{{}}}",
                kv.iter()
                    .map(|(k, v)| format!("{}:{}", Json::Str(k.clone()).render(), v.render()))
                    .collect::<Vec<_>>()
                    .join(",")
            ),
        }
    }
}

pub fn parse_json(s: &str) -> Option<Json> {
    let b: Vec<char> = s.chars().collect();
    let mut i = 0;
    let v = value(&b, &mut i)?;
    Some(v)
}

fn ws(b: &[char], i: &mut usize) {
    while *i < b.len() && b[*i].is_whitespace() {
        *i += 1;
    }
}

fn value(b: &[char], i: &mut usize) -> Option<Json> {
    ws(b, i);
    match *b.get(*i)? {
        'n' => lit(b, i, "null", Json::Null),
        't' => lit(b, i, "true", Json::Bool(true)),
        'f' => lit(b, i, "false", Json::Bool(false)),
        '"' => string(b, i).map(Json::Str),
        '[' => {
            *i += 1;
            let mut out = Vec::new();
            loop {
                ws(b, i);
                if *b.get(*i)? == ']' {
                    *i += 1;
                    return Some(Json::Arr(out));
                }
                out.push(value(b, i)?);
                ws(b, i);
                if *b.get(*i)? == ',' {
                    *i += 1;
                }
            }
        }
        '{' => {
            *i += 1;
            let mut out = Vec::new();
            loop {
                ws(b, i);
                if *b.get(*i)? == '}' {
                    *i += 1;
                    return Some(Json::Obj(out));
                }
                let k = string(b, i)?;
                ws(b, i);
                if *b.get(*i)? != ':' {
                    return None;
                }
                *i += 1;
                out.push((k, value(b, i)?));
                ws(b, i);
                if *b.get(*i)? == ',' {
                    *i += 1;
                }
            }
        }
        _ => {
            let start = *i;
            while *i < b.len() && (b[*i].is_ascii_digit() || "+-.eE".contains(b[*i])) {
                *i += 1;
            }
            b[start..*i]
                .iter()
                .collect::<String>()
                .parse()
                .ok()
                .map(Json::Num)
        }
    }
}

fn lit(b: &[char], i: &mut usize, word: &str, v: Json) -> Option<Json> {
    let end = *i + word.len();
    if b.get(*i..end)?.iter().collect::<String>() == word {
        *i = end;
        Some(v)
    } else {
        None
    }
}

fn string(b: &[char], i: &mut usize) -> Option<String> {
    if *b.get(*i)? != '"' {
        return None;
    }
    *i += 1;
    let mut s = String::new();
    loop {
        let c = *b.get(*i)?;
        *i += 1;
        match c {
            '"' => return Some(s),
            '\\' => {
                let e = *b.get(*i)?;
                *i += 1;
                match e {
                    'n' => s.push('\n'),
                    't' => s.push('\t'),
                    'r' => s.push('\r'),
                    'b' => s.push('\u{8}'),
                    'f' => s.push('\u{c}'),
                    'u' => {
                        let hex: String = b.get(*i..*i + 4)?.iter().collect();
                        *i += 4;
                        s.push(char::from_u32(u32::from_str_radix(&hex, 16).ok()?)?);
                    }
                    c => s.push(c),
                }
            }
            c => s.push(c),
        }
    }
}

// ---- diagnostics ----

/// The errors of a document: `(line, column, message)`, zero-based positions.
pub fn diagnostics(src: &str) -> Vec<(usize, usize, usize, String)> {
    let at = |span: apex_span::Span, msg: String| {
        let (l, c) = span.line_col(src);
        let (el, ec) = apex_span::Span::new(span.end as usize, span.end as usize).line_col(src);
        let _ = (el, ec);
        (
            l - 1,
            c - 1,
            (span.end.saturating_sub(span.start)) as usize,
            msg,
        )
    };
    let module = match apex_syntax::parse(src) {
        Ok(m) => m,
        Err(e) => return vec![at(e.span, e.msg)],
    };
    let mut el = apex_elab::Elaborator::new();
    el.load_libs_for(src);
    match el.elab_module(&module) {
        Ok(()) => vec![],
        Err(e) => vec![at(e.span, e.msg)],
    }
}

fn read_message(input: &mut impl BufRead) -> Option<Json> {
    let mut len = None;
    loop {
        let mut line = String::new();
        if input.read_line(&mut line).ok()? == 0 {
            return None;
        }
        let line = line.trim();
        if line.is_empty() {
            break;
        }
        if let Some(v) = line.strip_prefix("Content-Length:") {
            len = v.trim().parse::<usize>().ok();
        }
    }
    let mut buf = vec![0u8; len?];
    input.read_exact(&mut buf).ok()?;
    parse_json(&String::from_utf8_lossy(&buf))
}

fn send(out: &mut impl Write, msg: &Json) {
    let body = msg.render();
    let _ = write!(out, "Content-Length: {}\r\n\r\n{}", body.len(), body);
    let _ = out.flush();
}

fn publish(out: &mut impl Write, uri: &str, src: &str) {
    let diags: Vec<Json> = diagnostics(src)
        .into_iter()
        .map(|(line, col, len, msg)| {
            let pos = |l: usize, c: usize| {
                Json::Obj(vec![
                    ("line".into(), Json::Num(l as f64)),
                    ("character".into(), Json::Num(c as f64)),
                ])
            };
            Json::Obj(vec![
                (
                    "range".into(),
                    Json::Obj(vec![
                        ("start".into(), pos(line, col)),
                        ("end".into(), pos(line, col + len.max(1))),
                    ]),
                ),
                ("severity".into(), Json::Num(1.0)),
                ("source".into(), Json::Str("apex".into())),
                ("message".into(), Json::Str(msg)),
            ])
        })
        .collect();
    send(
        out,
        &Json::Obj(vec![
            ("jsonrpc".into(), Json::Str("2.0".into())),
            (
                "method".into(),
                Json::Str("textDocument/publishDiagnostics".into()),
            ),
            (
                "params".into(),
                Json::Obj(vec![
                    ("uri".into(), Json::Str(uri.into())),
                    ("diagnostics".into(), Json::Arr(diags)),
                ]),
            ),
        ]),
    );
}

pub fn run() {
    // elaboration recurses deeply: run on a big stack
    let t = std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(serve)
        .expect("start the language server");
    let _ = t.join();
}

fn serve() {
    let stdin = std::io::stdin();
    let mut input = stdin.lock();
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    let mut docs: HashMap<String, String> = HashMap::new();
    while let Some(msg) = read_message(&mut input) {
        let method = msg
            .get("method")
            .and_then(Json::str)
            .unwrap_or("")
            .to_string();
        let id = msg.get("id").cloned();
        let params = msg.get("params").cloned().unwrap_or(Json::Null);
        let doc_uri = params
            .get("textDocument")
            .and_then(|d| d.get("uri"))
            .and_then(Json::str)
            .map(str::to_string);
        match method.as_str() {
            "initialize" => send(
                &mut out,
                &Json::Obj(vec![
                    ("jsonrpc".into(), Json::Str("2.0".into())),
                    ("id".into(), id.unwrap_or(Json::Null)),
                    (
                        "result".into(),
                        Json::Obj(vec![
                            (
                                "capabilities".into(),
                                Json::Obj(vec![("textDocumentSync".into(), Json::Num(1.0))]),
                            ),
                            (
                                "serverInfo".into(),
                                Json::Obj(vec![("name".into(), Json::Str("apex".into()))]),
                            ),
                        ]),
                    ),
                ]),
            ),
            "textDocument/didOpen" => {
                if let (Some(uri), Some(text)) = (
                    doc_uri,
                    params
                        .get("textDocument")
                        .and_then(|d| d.get("text"))
                        .and_then(Json::str),
                ) {
                    docs.insert(uri.clone(), text.to_string());
                    publish(&mut out, &uri, text);
                }
            }
            "textDocument/didChange" => {
                let text = match params.get("contentChanges") {
                    Some(Json::Arr(cs)) => {
                        cs.last().and_then(|c| c.get("text")).and_then(Json::str)
                    }
                    _ => None,
                };
                if let (Some(uri), Some(text)) = (doc_uri, text) {
                    docs.insert(uri.clone(), text.to_string());
                    publish(&mut out, &uri, text);
                }
            }
            "textDocument/didSave" => {
                if let Some(uri) = doc_uri {
                    if let Some(text) = docs.get(&uri).cloned() {
                        publish(&mut out, &uri, &text);
                    }
                }
            }
            "textDocument/didClose" => {
                if let Some(uri) = doc_uri {
                    docs.remove(&uri);
                    publish(&mut out, &uri, "");
                }
            }
            "shutdown" => send(
                &mut out,
                &Json::Obj(vec![
                    ("jsonrpc".into(), Json::Str("2.0".into())),
                    ("id".into(), id.unwrap_or(Json::Null)),
                    ("result".into(), Json::Null),
                ]),
            ),
            "exit" => return,
            _ => {
                // unknown request: answer with an empty result so clients do not wait
                if let Some(id) = id {
                    send(
                        &mut out,
                        &Json::Obj(vec![
                            ("jsonrpc".into(), Json::Str("2.0".into())),
                            ("id".into(), id),
                            ("result".into(), Json::Null),
                        ]),
                    );
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn json_round_trip() {
        let j = parse_json(r#"{"a":[1,2,{"b":"x\ny"}],"c":null,"d":true}"#).unwrap();
        assert_eq!(parse_json(&j.render()).unwrap(), j);
    }

    #[test]
    fn reports_an_error_with_its_position() {
        let d = diagnostics("fn f() -> Nat { true }\n");
        assert_eq!(d.len(), 1);
        assert_eq!(d[0].0, 0);
    }
}
