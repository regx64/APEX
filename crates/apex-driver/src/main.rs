use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("lex") if args.len() == 3 => lex_file(&args[2]),
        _ => {
            eprintln!("usage: apex lex <file.apex>");
            ExitCode::from(2)
        }
    }
}

fn lex_file(path: &str) -> ExitCode {
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {path}: {e}");
            return ExitCode::FAILURE;
        }
    };
    match apex_syntax::lex(&src) {
        Ok(toks) => {
            for t in toks {
                println!("{:?} @ {}..{}", t.kind, t.span.start, t.span.end);
            }
            ExitCode::SUCCESS
        }
        Err(e) => {
            let (l, c) = e.span.line_col(&src);
            eprintln!("error: {path}:{l}:{c}: {}", e.msg);
            ExitCode::FAILURE
        }
    }
}
