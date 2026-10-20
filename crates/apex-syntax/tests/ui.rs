//! Runs every `tests/ui/ok/*.apex` (must parse) and `tests/ui/err/*.apex`
//! (first line `// expect: <substring>` must appear in the error message).

use std::fs;
use std::path::PathBuf;

fn files(sub: &str) -> Vec<PathBuf> {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/ui")
        .join(sub);
    let mut v: Vec<_> = fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .collect();
    v.sort();
    v
}

#[test]
fn ok_files_parse() {
    let paths = files("ok");
    assert!(!paths.is_empty());
    for p in paths {
        let src = fs::read_to_string(&p).unwrap();
        if let Err(e) = apex_syntax::parse(&src) {
            panic!(
                "{}",
                apex_span::render_diagnostic(&p.display().to_string(), &src, &e.msg, e.span)
            );
        }
    }
}

#[test]
fn err_files_report_expected_message() {
    let paths = files("err");
    assert!(!paths.is_empty());
    for p in paths {
        let src = fs::read_to_string(&p).unwrap();
        let want = src
            .lines()
            .next()
            .unwrap()
            .strip_prefix("// expect: ")
            .expect("missing `// expect:` header");
        let e = apex_syntax::parse(&src).expect_err(&format!("{} should fail", p.display()));
        assert!(
            e.msg.contains(want),
            "{}: got `{}`, wanted `{want}`",
            p.display(),
            e.msg
        );
    }
}
