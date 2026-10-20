//! `tests/ui/check/ok/*.apex` must elaborate and pass the kernel;
//! `tests/ui/check/err/*.apex` must fail with the message in their `// expect:` header.

use std::fs;
use std::path::PathBuf;

fn files(sub: &str) -> Vec<PathBuf> {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/ui/check")
        .join(sub);
    let mut v: Vec<_> = fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .collect();
    v.sort();
    v
}

#[test]
fn ok_files_check() {
    let paths = files("ok");
    assert!(!paths.is_empty());
    for p in paths {
        let src = fs::read_to_string(&p).unwrap();
        if let Err(d) = apex_elab::check_source(&p.display().to_string(), &src) {
            panic!("{d}");
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
        match apex_elab::check_source(&p.display().to_string(), &src) {
            Ok(_) => panic!("{} should fail", p.display()),
            Err(d) => assert!(
                d.contains(want),
                "{}: wanted `{want}` in:\n{d}",
                p.display()
            ),
        }
    }
}
