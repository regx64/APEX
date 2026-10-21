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
        (Some("run"), Some(path)) => run(path, |src| match apex_eval::run_source(path, src) {
            Ok(out) => {
                println!("{out}");
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
        _ => {
            eprintln!("usage: apex <lex|parse|check|run> <file.apex>");
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
