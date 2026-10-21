mod doc;
mod project;
mod repl;

use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    match (args.get(1).map(String::as_str), args.get(2)) {
        (Some("lex"), Some(path)) => run(path, |src| {
            let toks = apex_syntax::lex(src).map_err(|e| (e.msg, e.span))?;
            for t in toks {
                println!("{:?} @ {}..{}", t.kind, t.span.start, t.span.end);
            }
            Ok(())
        }),
        (Some("parse"), Some(path)) => run(path, |src| {
            let m = apex_syntax::parse(src).map_err(|e| (e.msg, e.span))?;
            println!("{m:#?}");
            Ok(())
        }),
        (Some("check"), Some(path)) => run(path, |src| match apex_elab::check_source(path, src) {
            Ok(_) => {
                println!("ok: {path}");
                Ok(())
            }
            Err(rendered) => {
                eprint!("{rendered}");
                Err((String::new(), apex_span::Span::default()))
            }
        }),
        (Some("verify"), Some(path)) => run(path, |src| match apex_elab::check_source(path, src) {
            Ok(el) => {
                // re-check every declaration with the independent verifier
                let no_accel = args.iter().any(|a| a == "--no-accel");
                let data = el.env().export();
                match apex_verify::verify(&data, apex_verify::Options { accel: !no_accel }) {
                    Ok(r) => {
                        println!(
                            "verified: {path} ({} axioms, {} definitions and theorems, {} inductive parts)",
                            r.axioms, r.definitions, r.inductive_parts
                        );
                        Ok(())
                    }
                    Err(msg) => Err((
                        format!("verification failed: {msg}"),
                        apex_span::Span::default(),
                    )),
                }
            }
            Err(rendered) => {
                eprint!("{rendered}");
                Err((String::new(), apex_span::Span::default()))
            }
        }),
        (Some("run"), Some(path)) => run(path, |src| match apex_eval::run_source(path, src) {
            Ok(out) => {
                print!("{out}");
                Ok(())
            }
            Err(rendered) => {
                eprint!("{rendered}");
                if !rendered.ends_with('\n') {
                    eprintln!();
                }
                Err((String::new(), apex_span::Span::default()))
            }
        }),
        (Some("doc"), Some(path)) => run(path, |src| match doc::generate(path, src) {
            Ok(md) => {
                print!("{md}");
                Ok(())
            }
            Err(msg) => Err((msg, apex_span::Span::default())),
        }),
        (Some("repl"), _) => {
            repl::run();
            ExitCode::SUCCESS
        }
        (Some("new"), Some(name)) => report(project::cmd_new(name)),
        (Some("build"), dir) => report(project::cmd_build(dir.map_or(".", |s| s.as_str()))),
        (Some("test"), dir) => report(project::cmd_test(dir.map_or(".", |s| s.as_str()))),
        (Some("run"), None) => report(project::cmd_run(".")),
        _ => {
            eprintln!(
                "usage: apex <lex|parse|check|verify|run|doc> <file.apex>\n       apex new <name> | build [dir] | run | test [dir] | repl"
            );
            ExitCode::from(2)
        }
    }
}

fn run(path: &str, f: impl FnOnce(&str) -> Result<(), (String, apex_span::Span)>) -> ExitCode {
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {path}: {e}");
            return ExitCode::FAILURE;
        }
    };
    match f(&src) {
        Ok(()) => ExitCode::SUCCESS,
        Err((msg, span)) => {
            // an empty message means the callee already printed its diagnostic
            if !msg.is_empty() {
                eprint!("{}", apex_span::render_diagnostic(path, &src, &msg, span));
            }
            ExitCode::FAILURE
        }
    }
}

fn report(r: Result<(), String>) -> ExitCode {
    match r {
        Ok(()) => ExitCode::SUCCESS,
        Err(msg) => {
            if !msg.is_empty() {
                eprint!("{msg}");
                if !msg.ends_with('\n') {
                    eprintln!();
                }
            }
            ExitCode::FAILURE
        }
    }
}
