//! Erasure and a lazy interpreter for checked APEX programs.

mod erase;
mod eval;

pub use eval::Evaluator;

use apex_kernel::Env;

/// Evaluate the global `main`. If it is an `IO` action, run it and return what
/// it printed; otherwise render its value. The result ends with a newline.
pub fn run_main(env: &Env) -> Result<String, String> {
    let Some(decl) = env.get("main") else {
        return Err("no `main` function: define `fn main() -> T { .. }`".into());
    };
    let (head, _) = apex_kernel::term::app_spine(decl.ty());
    let is_io = matches!(&*head, apex_kernel::Term::Const(n, _) if &**n == "IO");
    let ev = Evaluator::new(env);
    let v = ev.global("main")?;
    if is_io {
        ev.run_io(v)?;
        Ok(ev.take_output())
    } else {
        Ok(format!("{}\n", ev.show(&v)?))
    }
}

/// Check and run a source file. Runs on a thread with a large stack because
/// the interpreter recurses deeply (lazy thunk chains, structural recursion).
pub fn run_source(path: &str, src: &str) -> Result<String, String> {
    let (path, src) = (path.to_string(), src.to_string());
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || {
            let el = apex_elab::check_source(&path, &src)?;
            run_main(el.env())
        })
        .map_err(|e| format!("cannot start interpreter thread: {e}"))?
        .join()
        .map_err(|_| "the interpreter crashed (stack overflow or internal error)".to_string())?
}
