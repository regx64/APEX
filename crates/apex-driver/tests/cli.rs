use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

fn apex() -> Command {
    Command::new(env!("CARGO_BIN_EXE_apex"))
}

fn scratch(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("apex-cli-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).unwrap();
    d
}

#[test]
fn project_lifecycle() {
    let dir = scratch("proj");
    let out = apex()
        .current_dir(&dir)
        .args(["new", "demo"])
        .output()
        .unwrap();
    assert!(out.status.success());
    let proj = dir.join("demo");
    let build = apex().current_dir(&proj).arg("build").output().unwrap();
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    assert!(String::from_utf8_lossy(&build.stdout).contains("2 files checked"));
    // nothing changed: the second build is a no-op
    let again = apex().current_dir(&proj).arg("build").output().unwrap();
    assert!(String::from_utf8_lossy(&again.stdout).contains("up to date"));
    let run = apex().current_dir(&proj).arg("run").output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), "hello from APEX\n");
    let test = apex().current_dir(&proj).arg("test").output().unwrap();
    assert!(test.status.success());
    assert!(String::from_utf8_lossy(&test.stdout).contains("1 passed, 0 failed"));
    // a failing proof in an imported module fails the build
    std::fs::write(
        proj.join("src/util.apex"),
        "fn double(n: Nat) -> Nat { n + n }\ntheorem bad(): double(1) = 3 := rfl\n",
    )
    .unwrap();
    let bad = apex().current_dir(&proj).arg("build").output().unwrap();
    assert!(!bad.status.success());
    assert!(String::from_utf8_lossy(&bad.stderr).contains("util.apex"));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn missing_module_is_reported() {
    let dir = scratch("nomod");
    apex()
        .current_dir(&dir)
        .args(["new", "demo"])
        .output()
        .unwrap();
    let proj = dir.join("demo");
    std::fs::write(
        proj.join("src/main.apex"),
        "import nothere;\nfn main() -> IO<Unit> { println(\"x\") }\n",
    )
    .unwrap();
    let out = apex().current_dir(&proj).arg("build").output().unwrap();
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("cannot find module `nothere`"));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn doc_lists_signatures_and_comments() {
    let dir = scratch("doc");
    let f = dir.join("m.apex");
    std::fs::write(&f, "/// Adds one.\nfn succ1(n: Nat) -> Nat { n + 1 }\n").unwrap();
    let out = apex().arg("doc").arg(&f).output().unwrap();
    let md = String::from_utf8_lossy(&out.stdout);
    assert!(md.contains("### fn succ1"), "{md}");
    assert!(md.contains("fn succ1(n: Nat) -> Nat"), "{md}");
    assert!(md.contains("Adds one."), "{md}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn repl_remembers_declarations() {
    let mut child = apex()
        .arg("repl")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(b"fn sq(n: Nat) -> Nat { n * n }\nsq(7)\n:type sq\n:quit\n")
        .unwrap();
    let out = child.wait_with_output().unwrap();
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(text.contains("49"), "{text}");
    assert!(text.contains("sq : Nat -> Nat"), "{text}");
}

/// The kernel computes `nat_sub`/`nat_div`/.. on literals directly; unfolding the library
/// definitions must give the same values (a grid of small cases checked both ways).
#[test]
fn nat_acceleration_agrees_with_the_definitions() {
    let dir = scratch("accel");
    let mut src = String::new();
    for a in 0..9u64 {
        for b in 0..9u64 {
            src += &format!(
                "theorem s_{a}_{b}(): {a} - {b} = {} := by {{ rfl }}\n",
                a.saturating_sub(b)
            );
            src += &format!(
                "theorem d_{a}_{b}(): {a} / {b} = {} := by {{ rfl }}\n",
                a.checked_div(b).unwrap_or(0)
            );
            src += &format!(
                "theorem r_{a}_{b}(): {a} % {b} = {} := by {{ rfl }}\n",
                if b == 0 { a } else { a % b }
            );
            src += &format!(
                "theorem e_{a}_{b}(): nat_beq({a}, {b}) = {} := by {{ rfl }}\n",
                a == b
            );
            src += &format!(
                "theorem l_{a}_{b}(): nat_lt({a}, {b}) = {} := by {{ rfl }}\n",
                a < b
            );
        }
    }
    let file = dir.join("grid.apex");
    std::fs::write(&file, src).unwrap();
    for no_accel in [false, true] {
        let mut cmd = apex();
        cmd.arg("check").arg(&file);
        if no_accel {
            cmd.env("APEX_NO_ACCEL", "1");
        }
        let out = cmd.output().unwrap();
        assert!(
            out.status.success(),
            "accel={}: {}",
            !no_accel,
            String::from_utf8_lossy(&out.stderr)
        );
    }
}

#[test]
fn verify_rechecks_everything_with_the_independent_verifier() {
    let dir = scratch("verify");
    let file = dir.join("v.apex");
    std::fs::write(
        &file,
        "theorem t(a: Nat, b: Nat): (a + b) * (a + b) = a * a + 2 * a * b + b * b := by { ring }\n",
    )
    .unwrap();
    let out = apex().arg("verify").arg(&file).output().unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(String::from_utf8_lossy(&out.stdout).contains("verified:"));
}

#[test]
fn compile_builds_a_native_executable_that_matches_the_interpreter() {
    if Command::new("cc").arg("--version").output().is_err() {
        return; // no C compiler on this machine
    }
    let dir = scratch("native");
    let src = dir.join("p.apex");
    std::fs::write(
        &src,
        "fn fib_iter(n: Nat, a: Nat, b: Nat) -> Nat { match n { 0 => a, Nat.succ(m) => fib_iter(m, b, a + b) } }\n\
         fn main() -> IO<Unit> { println(Nat.toString(fib_iter(15, 0, 1))) }\n",
    )
    .unwrap();
    let exe = dir.join("p");
    let out = apex()
        .arg("compile")
        .arg(&src)
        .arg("-o")
        .arg(&exe)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let native = Command::new(&exe).output().unwrap();
    let interp = apex().arg("run").arg(&src).output().unwrap();
    assert_eq!(native.stdout, interp.stdout);
    assert_eq!(String::from_utf8_lossy(&native.stdout), "610\n");
}

#[test]
fn lsp_publishes_diagnostics() {
    let mut child = apex()
        .arg("lsp")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let frame = |body: &str| format!("Content-Length: {}\r\n\r\n{}", body.len(), body);
    let text = "fn f() -> Nat { true }\\n";
    let msgs = [
        r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#.to_string(),
        format!(
            r#"{{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{{"textDocument":{{"uri":"file:///a.apex","text":"{text}"}}}}}}"#
        ),
        r#"{"jsonrpc":"2.0","id":2,"method":"shutdown"}"#.to_string(),
        r#"{"jsonrpc":"2.0","method":"exit"}"#.to_string(),
    ];
    let mut stdin = child.stdin.take().unwrap();
    for m in &msgs {
        stdin.write_all(frame(m).as_bytes()).unwrap();
    }
    drop(stdin);
    let out = child.wait_with_output().unwrap();
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(text.contains("publishDiagnostics"), "{text}");
    assert!(text.contains("type mismatch"), "{text}");
}
