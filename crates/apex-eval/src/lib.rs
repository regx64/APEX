//! Erasure and a lazy interpreter for checked APEX programs.

mod erase;
mod eval;

pub use eval::Evaluator;

use apex_kernel::Env;

/// Evaluate the global `main` and render its value.
pub fn run_main(env: &Env) -> Result<String, String> {
    if env.get("main").is_none() {
        return Err("no `main` function: define `fn main() -> T { .. }`".into());
    }
    let ev = Evaluator::new(env);
    let v = ev.global("main")?;
    ev.show(&v)
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
