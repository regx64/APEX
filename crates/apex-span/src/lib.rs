//! Source positions shared by all compiler stages.

/// Half-open byte range `[start, end)` into a source file.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Span {
            start: start as u32,
            end: end as u32,
        }
    }

    pub fn len(&self) -> usize {
        (self.end - self.start) as usize
    }

    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

    pub fn to(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    /// 1-based (line, column) of `start` within `src`; columns count chars.
    pub fn line_col(&self, src: &str) -> (usize, usize) {
        let before = &src[..self.start as usize];
        let line = before.matches('\n').count() + 1;
        let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
        (line, col)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn line_col_works() {
        let src = "ab\ncd";
        assert_eq!(Span::new(4, 5).line_col(src), (2, 2));
    }
}

/// Render an error with a source excerpt, in the style of rustc.
pub fn render_diagnostic(path: &str, src: &str, msg: &str, span: Span) -> String {
    let (line, col) = span.line_col(src);
    let text = src.lines().nth(line - 1).unwrap_or("");
    let pad = " ".repeat(line.to_string().len());
    let end = (span.end as usize).min(src.len());
    let width = src[span.start as usize..end]
        .chars()
        .take_while(|&c| c != '\n')
        .count()
        .max(1);
    format!(
        "error: {msg}\n{pad}--> {path}:{line}:{col}\n{pad} |\n{line} | {text}\n{pad} | {}{}\n",
        " ".repeat(col - 1),
        "^".repeat(width)
    )
}

#[cfg(test)]
mod render_tests {
    use super::*;

    #[test]
    fn renders_caret() {
        let out = render_diagnostic("a.apex", "let x;\nfoo bar", "bad", Span::new(11, 14));
        assert_eq!(
            out,
            "error: bad\n --> a.apex:2:5\n  |\n2 | foo bar\n  |     ^^^\n"
        );
    }
}
