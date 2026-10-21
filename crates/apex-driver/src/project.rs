//! Projects: `apex.toml`, `import` resolution, and the `build` / `run` / `test` / `new` commands.

use apex_syntax::ast::ItemKind;
use std::collections::HashSet;
use std::path::{Path, PathBuf};

pub struct Manifest {
    pub name: String,
    pub version: String,
    /// The entry file, relative to the project root.
    pub main: String,
    /// The directory `import a.b;` is resolved against (`a/b.apex` inside it).
    pub src: String,
}

/// A tiny `key = "value"` reader for the `[package]` table.
pub fn read_manifest(root: &Path) -> Result<Manifest, String> {
    let path = root.join("apex.toml");
    let text = std::fs::read_to_string(&path)
        .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
    let mut m = Manifest {
        name: String::new(),
        version: "0.1.0".into(),
        main: "src/main.apex".into(),
        src: "src".into(),
    };
    for line in text.lines() {
        let line = line.split('#').next().unwrap_or("").trim();
        let Some((k, v)) = line.split_once('=') else {
            continue;
        };
        let v = v.trim().trim_matches('"').to_string();
        match k.trim() {
            "name" => m.name = v,
            "version" => m.version = v,
            "main" => m.main = v,
            "src" => m.src = v,
            _ => {}
        }
    }
    if m.name.is_empty() {
        return Err(format!("{}: missing `name`", path.display()));
    }
    Ok(m)
}

/// Find the project root: `dir` or the nearest ancestor containing `apex.toml`.
pub fn find_root(dir: &Path) -> Option<PathBuf> {
    let mut cur = std::fs::canonicalize(dir).ok()?;
    loop {
        if cur.join("apex.toml").exists() {
            return Some(cur);
        }
        if !cur.pop() {
            return None;
        }
    }
}

/// Load `entry` and everything it imports, dependencies first.
pub fn load(entry: &Path, src_dir: &Path) -> Result<Vec<(String, String)>, String> {
    fn go(
        path: &Path,
        src_dir: &Path,
        seen: &mut HashSet<PathBuf>,
        stack: &mut Vec<PathBuf>,
        out: &mut Vec<(String, String)>,
    ) -> Result<(), String> {
        let canon = std::fs::canonicalize(path)
            .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
        if seen.contains(&canon) {
            return Ok(());
        }
        if stack.contains(&canon) {
            return Err(format!("import cycle through {}", path.display()));
        }
        let text = std::fs::read_to_string(path)
            .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
        let module = apex_syntax::parse(&text).map_err(|e| {
            apex_span::render_diagnostic(&path.display().to_string(), &text, &e.msg, e.span)
        })?;
        stack.push(canon.clone());
        for item in &module.items {
            if let ItemKind::Import(name) = &item.kind {
                let rel = format!("{}.apex", name.replace('.', "/"));
                let dep = src_dir.join(rel);
                if !dep.exists() {
                    return Err(apex_span::render_diagnostic(
                        &path.display().to_string(),
                        &text,
                        &format!(
                            "cannot find module `{name}` ({} does not exist)",
                            dep.display()
                        ),
                        item.span,
                    ));
                }
                go(&dep, src_dir, seen, stack, out)?;
            }
        }
        stack.pop();
        seen.insert(canon);
        out.push((path.display().to_string(), text));
        Ok(())
    }
    let mut out = Vec::new();
    go(
        entry,
        src_dir,
        &mut HashSet::new(),
        &mut Vec::new(),
        &mut out,
    )?;
    Ok(out)
}

fn apex_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(rd) = std::fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<_> = rd.flatten().map(|e| e.path()).collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            apex_files(&p, out);
        } else if p.extension().is_some_and(|e| e == "apex") {
            out.push(p);
        }
    }
}

pub struct Project {
    pub root: PathBuf,
    pub manifest: Manifest,
}

impl Project {
    pub fn open(dir: &str) -> Result<Project, String> {
        let root = find_root(Path::new(dir))
            .ok_or_else(|| format!("no apex.toml found in `{dir}` or its parents"))?;
        let manifest = read_manifest(&root)?;
        Ok(Project { root, manifest })
    }

    fn src_dir(&self) -> PathBuf {
        self.root.join(&self.manifest.src)
    }

    /// Every file of the project the build checks: all of `src/`, imports first.
    pub fn all_files(&self) -> Result<Vec<(String, String)>, String> {
        let mut out: Vec<(String, String)> = Vec::new();
        let mut entries = vec![self.root.join(&self.manifest.main)];
        let mut found = Vec::new();
        apex_files(&self.src_dir(), &mut found);
        entries.extend(found);
        for e in entries {
            if !e.exists() {
                continue;
            }
            for f in load(&e, &self.src_dir())? {
                if !out.iter().any(|(p, _)| *p == f.0) {
                    out.push(f);
                }
            }
        }
        Ok(out)
    }
}

pub fn cmd_new(name: &str) -> Result<(), String> {
    let root = Path::new(name);
    if root.exists() {
        return Err(format!("`{name}` already exists"));
    }
    std::fs::create_dir_all(root.join("src")).map_err(|e| e.to_string())?;
    std::fs::create_dir_all(root.join("tests")).map_err(|e| e.to_string())?;
    let w = |p: PathBuf, s: String| std::fs::write(p, s).map_err(|e| e.to_string());
    w(
        root.join("apex.toml"),
        format!("[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nmain = \"src/main.apex\"\nsrc = \"src\"\n"),
    )?;
    w(
        root.join("src/main.apex"),
        "import util;\n\nfn main() -> IO<Unit> {\n    println(\"hello from APEX\")\n}\n".into(),
    )?;
    w(
        root.join("src/util.apex"),
        "fn double(n: Nat) -> Nat { n + n }\n\ntheorem double_zero(): double(0) = 0 := rfl\n"
            .into(),
    )?;
    w(
        root.join("tests/basic.apex"),
        "// out: 6\nimport util;\n\nfn main() -> IO<Unit> {\n    println(Nat.toString(double(3)))\n}\n".into(),
    )?;
    println!("created project `{name}`");
    Ok(())
}

pub fn cmd_build(dir: &str) -> Result<(), String> {
    let p = Project::open(dir)?;
    let files = p.all_files()?;
    apex_elab::check_files(&files)?;
    println!(
        "ok: {} v{} ({} files checked)",
        p.manifest.name,
        p.manifest.version,
        files.len()
    );
    Ok(())
}

pub fn cmd_run(dir: &str) -> Result<(), String> {
    let p = Project::open(dir)?;
    let files = load(&p.root.join(&p.manifest.main), &p.src_dir())?;
    print!("{}", apex_eval::run_files(&files)?);
    Ok(())
}

/// Check the project, then run every `tests/*.apex` and compare against its
/// `// out:` lines (a test without them only has to run).
pub fn cmd_test(dir: &str) -> Result<(), String> {
    let p = Project::open(dir)?;
    apex_elab::check_files(&p.all_files()?)?;
    let mut tests = Vec::new();
    apex_files(&p.root.join("tests"), &mut tests);
    let (mut passed, mut failed) = (0, 0);
    for t in tests {
        let name = t.display().to_string();
        let result = load(&t, &p.src_dir()).and_then(|files| {
            let expected: Vec<String> = files
                .last()
                .map(|(_, s)| {
                    s.lines()
                        .filter_map(|l| l.strip_prefix("// out:"))
                        .map(|l| l.strip_prefix(' ').unwrap_or(l).to_string())
                        .collect()
                })
                .unwrap_or_default();
            let got = apex_eval::run_files(&files)?;
            if expected.is_empty() || got == format!("{}\n", expected.join("\n")) {
                Ok(())
            } else {
                Err(format!("expected:\n{}\ngot:\n{got}", expected.join("\n")))
            }
        });
        match result {
            Ok(()) => {
                passed += 1;
                println!("PASS {name}");
            }
            Err(e) => {
                failed += 1;
                println!("FAIL {name}\n{e}");
            }
        }
    }
    println!("{passed} passed, {failed} failed");
    if failed > 0 {
        Err(String::new())
    } else {
        Ok(())
    }
}
