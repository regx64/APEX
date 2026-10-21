//! Every `tests/run/*.apex` is checked and run; its stdout must equal the
//! `// out: <value>` header.

use std::fs;
use std::path::PathBuf;

fn dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/run")
}

#[test]
fn programs_print_expected_output() {
    let mut paths: Vec<_> = fs::read_dir(dir())
        .unwrap()
        .map(|e| e.unwrap().path())
        .collect();
    paths.sort();
    assert!(paths.len() >= 5);
    for p in paths {
        let src = fs::read_to_string(&p).unwrap();
        let want = src
            .lines()
            .next()
            .unwrap()
            .strip_prefix("// out: ")
            .expect("missing `// out:` header");
        match apex_eval::run_source(&p.display().to_string(), &src) {
            Ok(got) => assert_eq!(got, want, "{}", p.display()),
            Err(e) => panic!("{} failed:\n{e}", p.display()),
        }
    }
}

#[test]
fn missing_main_is_reported() {
    let err = apex_eval::run_source("t.apex", "fn f() -> Nat { 1 }").unwrap_err();
    assert!(err.contains("no `main`"), "{err}");
}

#[test]
fn type_errors_stop_before_running() {
    let err = apex_eval::run_source("t.apex", "fn main() -> Nat { true }").unwrap_err();
    assert!(err.contains("type mismatch"), "{err}");
}

#[test]
fn nat_overflow_is_an_error_not_a_wrap() {
    let src = "fn pow2(n: Nat) -> Nat { match n { 0 => 1, Nat.succ(m) => 2 * pow2(m) } }\nfn main() -> Nat { pow2(200) }";
    let err = apex_eval::run_source("t.apex", src).unwrap_err();
    assert!(err.contains("overflow"), "{err}");
}
