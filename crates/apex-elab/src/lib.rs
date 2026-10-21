//! Elaborator: surface syntax to kernel terms.
//!
//! Elaboration may leave metavariables in terms; every produced declaration
//! is zonked and then re-checked by the kernel with a clean type checker, so
//! nothing here needs to be trusted.

mod elab;

pub use elab::{ElabError, Elaborator};

use apex_span::{render_diagnostic, render_full};

/// Parse, elaborate and kernel-check a whole source file against the prelude.
/// On failure returns a rendered diagnostic.
pub fn check_source(path: &str, src: &str) -> Result<Elaborator, String> {
    let module =
        apex_syntax::parse(src).map_err(|e| render_diagnostic(path, src, &e.msg, e.span))?;
    let mut el = Elaborator::new();
    el.load_libs_for(src);
    el.elab_module(&module)
        .map_err(|e| render_full(path, src, e.code.as_deref(), &e.msg, e.span, &e.notes))?;
    Ok(el)
}

/// Check several files in order (dependencies first), sharing one environment.
/// Each file is a `(path, source)` pair; a failure is rendered against its own file.
pub fn check_files(files: &[(String, String)]) -> Result<Elaborator, String> {
    let mut el = Elaborator::new();
    for (_, src) in files {
        el.load_libs_for(src);
    }
    for (path, src) in files {
        let module =
            apex_syntax::parse(src).map_err(|e| render_diagnostic(path, src, &e.msg, e.span))?;
        el.elab_module(&module)
            .map_err(|e| render_full(path, src, e.code.as_deref(), &e.msg, e.span, &e.notes))?;
    }
    Ok(el)
}
