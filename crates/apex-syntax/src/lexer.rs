//! Hand-written lexer for APEX.

use apex_span::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Ident(String),
    Nat(u64),
    Str(String),
    Lifetime(String),
    // keywords
    Fn,
    Struct,
    Enum,
    Trait,
    Impl,
    Theorem,
    Let,
    Match,
    By,
    Own,
    Mut,
    Unsafe,
    For,
    If,
    Else,
    Do,
    In,
    // punctuation
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Semi,
    Colon,
    ColonEq,
    Arrow,
    /// `<-`, binding the result of an action inside `do`.
    LArrow,
    FatArrow,
    Amp,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    PlusEq,
    MinusEq,
    StarEq,
    SlashEq,
    PercentEq,
    Eq,
    EqEq,
    Dot,
    Lt,
    Gt,
    Bar,
    Underscore,
    Eof,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LexError {
    pub msg: String,
    pub span: Span,
}

fn keyword(s: &str) -> Option<TokenKind> {
    use TokenKind::*;
    Some(match s {
        "fn" => Fn,
        "struct" => Struct,
        "enum" => Enum,
        "trait" => Trait,
        "impl" => Impl,
        "theorem" => Theorem,
        "let" => Let,
        "match" => Match,
        "by" => By,
        "own" => Own,
        "mut" => Mut,
        "unsafe" => Unsafe,
        "for" => For,
        "if" => If,
        "else" => Else,
        "do" => Do,
        "in" => In,
        "_" => Underscore,
        _ => return None,
    })
}

/// Tokenize `src`. The result always ends with an `Eof` token.
pub fn lex(src: &str) -> Result<Vec<Token>, LexError> {
    use TokenKind::*;
    let b = src.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();
    while i < b.len() {
        let c = b[i];
        let start = i;
        // whitespace
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        // comments: `//` line, `/* */` nested block
        if c == b'/' && b.get(i + 1) == Some(&b'/') {
            while i < b.len() && b[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        if c == b'/' && b.get(i + 1) == Some(&b'*') {
            let mut depth = 1;
            i += 2;
            while depth > 0 {
                match (b.get(i), b.get(i + 1)) {
                    (Some(b'/'), Some(b'*')) => {
                        depth += 1;
                        i += 2
                    }
                    (Some(b'*'), Some(b'/')) => {
                        depth -= 1;
                        i += 2
                    }
                    (Some(_), _) => i += 1,
                    (None, _) => {
                        return Err(LexError {
                            msg: "unterminated block comment".into(),
                            span: Span::new(start, b.len()),
                        })
                    }
                }
            }
            continue;
        }
        let kind = if c.is_ascii_digit() {
            while i < b.len() && (b[i].is_ascii_digit() || b[i] == b'_') {
                i += 1;
            }
            let text: String = src[start..i].chars().filter(|&c| c != '_').collect();
            Nat(text.parse().map_err(|_| LexError {
                msg: "integer literal too large".into(),
                span: Span::new(start, i),
            })?)
        } else if c == b'_' || c.is_ascii_alphabetic() {
            while i < b.len() && (b[i] == b'_' || b[i] == b'\'' || b[i].is_ascii_alphanumeric()) {
                i += 1;
            }
            let s = &src[start..i];
            keyword(s).unwrap_or_else(|| Ident(s.to_string()))
        } else if c == b'\'' {
            i += 1;
            let name_start = i;
            while i < b.len() && (b[i] == b'_' || b[i].is_ascii_alphanumeric()) {
                i += 1;
            }
            if i == name_start {
                return Err(LexError {
                    msg: "expected lifetime name after `'`".into(),
                    span: Span::new(start, i),
                });
            }
            Lifetime(src[start..i].to_string())
        } else if c == b'"' {
            i += 1;
            let mut s = String::new();
            loop {
                match b.get(i) {
                    None => {
                        return Err(LexError {
                            msg: "unterminated string".into(),
                            span: Span::new(start, b.len()),
                        })
                    }
                    Some(b'"') => {
                        i += 1;
                        break;
                    }
                    Some(b'\\') => {
                        let e = match b.get(i + 1) {
                            Some(b'n') => '\n',
                            Some(b't') => '\t',
                            Some(b'"') => '"',
                            Some(b'\\') => '\\',
                            _ => {
                                return Err(LexError {
                                    msg: "invalid escape".into(),
                                    span: Span::new(i, i + 2),
                                })
                            }
                        };
                        s.push(e);
                        i += 2;
                    }
                    Some(_) => {
                        let ch = src[i..].chars().next().unwrap();
                        s.push(ch);
                        i += ch.len_utf8();
                    }
                }
            }
            Str(s)
        } else {
            let two = b.get(i + 1).copied();
            let (k, n) = match (c, two) {
                (b':', Some(b'=')) => (ColonEq, 2),
                (b'-', Some(b'>')) => (Arrow, 2),
                (b'+', Some(b'=')) => (PlusEq, 2),
                (b'-', Some(b'=')) => (MinusEq, 2),
                (b'*', Some(b'=')) => (StarEq, 2),
                (b'/', Some(b'=')) => (SlashEq, 2),
                (b'%', Some(b'=')) => (PercentEq, 2),
                (b'<', Some(b'-')) => (LArrow, 2),
                (b'=', Some(b'>')) => (FatArrow, 2),
                (b'=', Some(b'=')) => (EqEq, 2),
                (b'(', _) => (LParen, 1),
                (b')', _) => (RParen, 1),
                (b'{', _) => (LBrace, 1),
                (b'}', _) => (RBrace, 1),
                (b'[', _) => (LBracket, 1),
                (b']', _) => (RBracket, 1),
                (b',', _) => (Comma, 1),
                (b';', _) => (Semi, 1),
                (b':', _) => (Colon, 1),
                (b'&', _) => (Amp, 1),
                (b'+', _) => (Plus, 1),
                (b'-', _) => (Minus, 1),
                (b'*', _) => (Star, 1),
                (b'/', _) => (Slash, 1),
                (b'%', _) => (Percent, 1),
                (b'=', _) => (Eq, 1),
                (b'.', _) => (Dot, 1),
                (b'<', _) => (Lt, 1),
                (b'>', _) => (Gt, 1),
                (b'|', _) => (Bar, 1),
                _ => {
                    let ch = src[i..].chars().next().unwrap();
                    return Err(LexError {
                        msg: format!("unexpected character `{ch}`"),
                        span: Span::new(i, i + ch.len_utf8()),
                    });
                }
            };
            i += n;
            k
        };
        out.push(Token {
            kind,
            span: Span::new(start, i),
        });
    }
    out.push(Token {
        kind: Eof,
        span: Span::new(b.len(), b.len()),
    });
    Ok(out)
}

impl std::fmt::Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TokenKind::*;
        let s = match self {
            Ident(s) => return write!(f, "identifier `{s}`"),
            Lifetime(s) => return write!(f, "lifetime `{s}`"),
            Nat(_) => "integer literal",
            Str(_) => "string literal",
            Eof => "end of file",
            Fn => "`fn`",
            Struct => "`struct`",
            Enum => "`enum`",
            Trait => "`trait`",
            Impl => "`impl`",
            Theorem => "`theorem`",
            Let => "`let`",
            Match => "`match`",
            By => "`by`",
            Own => "`own`",
            Mut => "`mut`",
            Unsafe => "`unsafe`",
            For => "`for`",
            If => "`if`",
            Else => "`else`",
            Do => "`do`",
            In => "`in`",
            LParen => "`(`",
            RParen => "`)`",
            LBrace => "`{`",
            RBrace => "`}`",
            LBracket => "`[`",
            RBracket => "`]`",
            Comma => "`,`",
            Semi => "`;`",
            Colon => "`:`",
            ColonEq => "`:=`",
            Arrow => "`->`",
            LArrow => "`<-`",
            FatArrow => "`=>`",
            Amp => "`&`",
            Plus => "`+`",
            Minus => "`-`",
            Star => "`*`",
            Slash => "`/`",
            Percent => "`%`",
            PlusEq => "`+=`",
            MinusEq => "`-=`",
            StarEq => "`*=`",
            SlashEq => "`/=`",
            PercentEq => "`%=`",
            Eq => "`=`",
            EqEq => "`==`",
            Dot => "`.`",
            Lt => "`<`",
            Gt => "`>`",
            Bar => "`|`",
            Underscore => "`_`",
        };
        f.write_str(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use TokenKind::*;

    fn kinds(s: &str) -> Vec<TokenKind> {
        lex(s).unwrap().into_iter().map(|t| t.kind).collect()
    }

    #[test]
    fn fn_signature() {
        assert_eq!(
            kinds("fn id(own x: Nat) -> Nat { x }"),
            vec![
                Fn,
                Ident("id".into()),
                LParen,
                Own,
                Ident("x".into()),
                Colon,
                Ident("Nat".into()),
                RParen,
                Arrow,
                Ident("Nat".into()),
                LBrace,
                Ident("x".into()),
                RBrace,
                Eof
            ]
        );
    }

    #[test]
    fn comments_and_literals() {
        assert_eq!(
            kinds("/* a /* b */ c */ 1_000 \"h\\n\" // x"),
            vec![Nat(1000), Str("h\n".into()), Eof]
        );
    }

    #[test]
    fn lifetimes() {
        assert_eq!(kinds("&'a mut"), vec![Amp, Lifetime("'a".into()), Mut, Eof]);
    }

    #[test]
    fn errors() {
        assert!(lex("\"abc").is_err());
        assert!(lex("/* x").is_err());
        assert!(lex("#").is_err());
    }
}
