//! A disk cache for the proofs of the bundled libraries.
//!
//! The libraries (`prelude_omega.apex`, `prelude_ring.apex`, ..) are large and their tactic
//! proofs take seconds to rebuild. After a library has been elaborated once, its theorem
//! values are stored (keyed by the hash of the library source and of this executable); the
//! next run elaborates only the *statements* and takes the proofs from the cache. A cached
//! proof is not re-checked, so the cache is trusted data: `APEX_NO_CACHE=1` turns it off, and
//! the independent verifier (`apex verify`) re-checks everything from scratch.

use apex_kernel::ser::{Reader, Writer};
use apex_kernel::T;
use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::path::PathBuf;

const MAGIC: &[u8] = b"APXC1";

pub struct LibCache {
    path: Option<PathBuf>,
    entries: HashMap<String, T>,
    fresh: Vec<(String, T)>,
}

fn build_id() -> u64 {
    let mut h = DefaultHasher::new();
    env!("CARGO_PKG_VERSION").hash(&mut h);
    if let Ok(exe) = std::env::current_exe() {
        if let Ok(m) = std::fs::metadata(&exe) {
            m.len().hash(&mut h);
            if let Ok(t) = m.modified() {
                t.hash(&mut h);
            }
        }
    }
    h.finish()
}

fn cache_dir() -> Option<PathBuf> {
    if std::env::var_os("APEX_NO_CACHE").is_some() {
        return None;
    }
    if let Some(d) = std::env::var_os("APEX_CACHE_DIR") {
        return Some(PathBuf::from(d));
    }
    let home = std::env::var_os("HOME")?;
    Some(PathBuf::from(home).join(".cache").join("apex"))
}

fn put_varint(out: &mut Vec<u8>, mut n: u64) {
    loop {
        let b = (n & 0x7f) as u8;
        n >>= 7;
        if n == 0 {
            out.push(b);
            return;
        }
        out.push(b | 0x80);
    }
}

fn get_varint(data: &[u8], pos: &mut usize) -> Option<u64> {
    let mut n = 0u64;
    let mut shift = 0;
    loop {
        let b = *data.get(*pos)?;
        *pos += 1;
        n |= ((b & 0x7f) as u64) << shift;
        if b & 0x80 == 0 {
            return Some(n);
        }
        shift += 7;
        if shift > 63 {
            return None;
        }
    }
}

impl LibCache {
    /// Open the cache of the library `id` with source `src`.
    pub fn open(id: &str, src: &str) -> LibCache {
        let mut h = DefaultHasher::new();
        src.hash(&mut h);
        build_id().hash(&mut h);
        let path = cache_dir().map(|d| d.join(format!("{id}-{:016x}.bin", h.finish())));
        let mut c = LibCache {
            path,
            entries: HashMap::new(),
            fresh: Vec::new(),
        };
        c.load();
        c
    }

    fn load(&mut self) {
        let Some(path) = &self.path else { return };
        let Ok(data) = std::fs::read(path) else {
            return;
        };
        let _ = (|| -> Option<()> {
            if !data.starts_with(MAGIC) {
                return None;
            }
            let mut pos = MAGIC.len();
            let count = get_varint(&data, &mut pos)? as usize;
            let mut roots = Vec::with_capacity(count);
            for _ in 0..count {
                let len = get_varint(&data, &mut pos)? as usize;
                let name = std::str::from_utf8(data.get(pos..pos + len)?)
                    .ok()?
                    .to_string();
                pos += len;
                let root = get_varint(&data, &mut pos)? as u32;
                roots.push((name, root));
            }
            let reader = Reader::new(&data[pos..]).ok()?;
            for (name, root) in roots {
                self.entries.insert(name, reader.term(root).ok()?);
            }
            Some(())
        })();
    }

    /// The cached proof of the theorem `name`.
    pub fn get(&self, name: &str) -> Option<T> {
        self.entries.get(name).cloned()
    }

    pub fn record(&mut self, name: &str, val: &T) {
        self.fresh.push((name.to_string(), val.clone()));
    }

    /// Write the cache if the run produced new proofs.
    pub fn save(self) {
        let (Some(path), false) = (&self.path, self.fresh.is_empty()) else {
            return;
        };
        let mut all: Vec<(String, T)> = self.entries.into_iter().collect();
        all.extend(self.fresh);
        let mut w = Writer::new();
        let roots: Vec<(String, u32)> = all.iter().map(|(n, t)| (n.clone(), w.term(t))).collect();
        let mut out = MAGIC.to_vec();
        put_varint(&mut out, roots.len() as u64);
        for (name, root) in &roots {
            put_varint(&mut out, name.len() as u64);
            out.extend_from_slice(name.as_bytes());
            put_varint(&mut out, *root as u64);
        }
        out.extend_from_slice(&w.finish());
        if let Some(dir) = path.parent() {
            let _ = std::fs::create_dir_all(dir);
        }
        // write atomically: a concurrent reader never sees a half-written file
        let tmp = path.with_extension(format!("tmp{}", std::process::id()));
        if std::fs::write(&tmp, &out).is_ok() {
            let _ = std::fs::rename(&tmp, path);
        }
    }
}
