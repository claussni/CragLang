// This file is part of Crag.
//
// Copyright (C) 2026 Ralf Claussnitzer
//
// Crag is free software: you can redistribute it and/or modify it under the
// terms of the GNU General Public License as published by the Free Software
// Foundation, either version 3 of the License, or (at your option) any later
// version.
//
// Crag is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
// A PARTICULAR PURPOSE. See the GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along with
// Crag. If not, see <https://www.gnu.org/licenses/>.

//! The persisted store (Implementation Plan §11.9.5): compiled code kept
//! in the settings directory's cache, by the hash of the compiler's
//! identity and everything Cranelift is given, so a second session and
//! the shell commands compile only what changed.
//!
//! A process that compiles holds the store's lock shared while it runs.
//! When it ends it records the artifacts it used as its project's roots,
//! and about once a day it collects the garbage, if no other process
//! holds the lock (§11.9.6).

use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

use crag_abi::CodeObject;
use crag_backend::CodeCache;
use crag_store::{ArtifactKey, LockMode, Store, StoreGuard};

/// How long an artifact no root names is kept, and how often garbage is
/// collected.
const DAY: Duration = Duration::from_secs(24 * 3600);

struct Persisted {
    store: Store,
    used: Mutex<Vec<ArtifactKey>>,
    hits: AtomicUsize,
    compiled: AtomicUsize,
    lock: Mutex<Option<StoreGuard>>,
}

static PERSISTED: std::sync::OnceLock<&'static Persisted> = std::sync::OnceLock::new();

struct Handle(&'static Persisted);

impl CodeCache for Handle {
    fn get(&self, input: &str) -> Option<CodeObject> {
        let p = self.0;
        let key = p.store.key("code").str(input).finish();
        p.used.lock().expect("not poisoned").push(key);
        let bytes = p.store.get(key).ok()??;
        let object = crag_session::protocol::decode_object(&bytes).ok()?;
        p.hits.fetch_add(1, Ordering::Relaxed);
        Some(object)
    }

    fn put(&self, input: &str, object: &CodeObject) {
        let p = self.0;
        p.compiled.fetch_add(1, Ordering::Relaxed);
        let key = p.store.key("code").str(input).finish();
        // Losing an artifact costs only a recompilation.
        let _ = p
            .store
            .put(key, &crag_session::protocol::encode_object(object));
    }
}

/// What tells this build of the compiler from others: its version and
/// its executable's size and time, so a rebuilt compiler starts afresh.
fn identity() -> String {
    let exe = std::env::current_exe().ok();
    let meta = exe.as_ref().and_then(|e| std::fs::metadata(e).ok());
    let stamp = meta
        .as_ref()
        .and_then(|m| m.modified().ok())
        .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
        .map_or(0, |d| d.as_nanos());
    format!(
        "crag {} {} {stamp}",
        env!("CARGO_PKG_VERSION"),
        meta.map_or(0, |m| m.len())
    )
}

/// The cache directory, below the settings directory.
pub fn cache_dir() -> Option<PathBuf> {
    crag_package::home::crag_home().map(|h| h.join("cache"))
}

/// Makes code generation use the persisted store, when the settings
/// directory has room for one. Without it, everything compiles as before.
pub fn install() {
    let Some(dir) = cache_dir() else {
        return;
    };
    let Ok(store) = Store::open(&dir, identity()) else {
        return;
    };
    let lock = store.lock(LockMode::Shared).ok();
    let persisted: &'static Persisted = Box::leak(Box::new(Persisted {
        store,
        used: Mutex::new(Vec::new()),
        hits: AtomicUsize::new(0),
        compiled: AtomicUsize::new(0),
        lock: Mutex::new(lock),
    }));
    if PERSISTED.set(persisted).is_ok() {
        crag_backend::install_code_cache(Box::new(Handle(persisted)));
    }
}

/// Ends the process's use of the store: records what the project at
/// `root` used, says how much was reused when `CRAG_CACHE_STATS` is set,
/// and collects the garbage when it is due.
pub fn finish(root: &Path) {
    let Some(p) = PERSISTED.get() else {
        return;
    };
    let used = std::mem::take(&mut *p.used.lock().expect("not poisoned"));
    let project = root.canonicalize().unwrap_or_else(|_| root.to_path_buf());
    if project.join("package.crag").is_file() && !used.is_empty() {
        let _ = p.store.set_roots(&project, &used);
    }
    if std::env::var_os("CRAG_CACHE_STATS").is_some() {
        eprintln!(
            "cache: {} reused, {} compiled",
            p.hits.load(Ordering::Relaxed),
            p.compiled.load(Ordering::Relaxed)
        );
    }
    let stamp = p.store.dir().join("collected");
    let due = std::fs::metadata(&stamp)
        .and_then(|m| m.modified())
        .map(|t| t.elapsed().unwrap_or_default() >= DAY)
        .unwrap_or(true);
    if due {
        // This process lets go of its share first.
        drop(p.lock.lock().expect("not poisoned").take());
        if let Ok(Some(_exclusive)) = p.store.try_lock(LockMode::Exclusive) {
            let _ = p.store.collect_garbage(DAY);
            let _ = std::fs::write(&stamp, "");
        }
    }
}
