//! `apex repl`: declarations accumulate; an expression is evaluated and printed.

use std::io::{BufRead, Write};

fn balanced(s: &str) -> bool {
    let (mut d, mut in_str) = (0i32, false);
    for c in s.chars() {
        match c {
            '"' => in_str = !in_str,
            '(' | '{' | '[' if !in_str => d += 1,
            ')' | '}' | ']' if !in_str => d -= 1,
            _ => {}
        }
    }
    d <= 0
}

const DECL_WORDS: &[&str] = &[
    "fn",
    "struct",
    "enum",
    "trait",
    "impl",
    "theorem",
    "namespace",
    "open",
    "section",
    "variable",
    "import",
    "#[simp]",
];

pub fn run() {
    println!(
        "APEX repl. Declarations are remembered; an expression is evaluated. :type NAME, :quit"
    );
    let stdin = std::io::stdin();
    let mut decls = String::new();
    let mut pending = String::new();
    loop {
        print!("{}", if pending.is_empty() { "> " } else { "| " });
        let _ = std::io::stdout().flush();
        let mut line = String::new();
        if stdin.lock().read_line(&mut line).unwrap_or(0) == 0 {
            break;
        }
        pending.push_str(&line);
        if !balanced(&pending) {
            continue;
        }
        let input = std::mem::take(&mut pending);
        let input = input.trim();
        if input.is_empty() {
            continue;
        }
        if input == ":quit" || input == ":q" {
            break;
        }
        if let Some(name) = input.strip_prefix(":type ") {
            match apex_elab::check_source("<repl>", &decls) {
                Ok(el) => match el.env().get(name.trim()) {
                    Some(d) => println!(
                        "{} : {}",
                        name.trim(),
                        apex_kernel::TypeChecker::new(el.env()).pp(d.ty())
                    ),
                    None => println!("unknown name `{}`", name.trim()),
                },
                Err(e) => print!("{e}"),
            }
            continue;
        }
        let first = input
            .split(|c: char| !c.is_alphanumeric() && c != '#' && c != '[' && c != ']')
            .next()
            .unwrap_or("");
        if DECL_WORDS.contains(&first) {
            let candidate = format!("{decls}\n{input}\n");
            match apex_elab::check_source("<repl>", &candidate) {
                Ok(_) => {
                    decls = candidate;
                    println!("ok");
                }
                Err(e) => print!("{e}"),
            }
        } else {
            let program = format!("{decls}\nfn main() -> IO<Unit> {{ display({input}) }}\n");
            match apex_eval::run_source("<repl>", &program) {
                Ok(out) => print!("{out}"),
                Err(e) => println!("{e}"),
            }
        }
    }
}
