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

//! Artifact store skeleton (Implementation Plan §11.3.8).
//!
//! BLAKE3 content-hash keys, hash-named blobs on disk, atomic writes by rename.
//!
//! An artifact is a result worth keeping across sessions: an item tree, an
//! inferred signature, MIR, a code object. Its key is a hash of everything
//! that determines it, so the same inputs never compile twice, and a changed
//! input simply produces a different key. Nothing is ever updated in place.
//!
//! # Layout on disk
//!
//! ```text
//! <dir>/ab/cdef...   one file per artifact, named by its key in hex
//! <dir>/tmp/         files being written
//! <dir>/roots/       for each project, the artifacts its last builds used
//! <dir>/lock         the file lock
//! ```
//!
//! Processes that build share the store under a shared lock; garbage
//! collection takes it exclusively, so it never removes what a build is
//! about to name in its roots (Implementation Plan §11.9.6). Readers need
//! no lock, since every write is an atomic rename.
//!
//! A file holds the BLAKE3 hash of the payload, then the payload. Writers
//! fill a temporary file and rename it into place. Renaming is atomic, so a
//! reader in this or another process sees either no file or a whole one.
//! The store does not force data to disk, since losing an artifact costs
//! only a recompilation; the hash catches a file a crash left incomplete,
//! and `get` then reports the artifact as missing.

use std::collections::HashSet;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, SystemTime};

const HASH_BYTES: usize = blake3::OUT_LEN;

/// Identifies an artifact: the hash of the inputs that determine it.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ArtifactKey([u8; HASH_BYTES]);

impl ArtifactKey {
    pub fn as_bytes(&self) -> &[u8; HASH_BYTES] {
        &self.0
    }

    /// The key as lowercase hex, which is also the artifact's file name.
    pub fn to_hex(&self) -> String {
        blake3::Hash::from_bytes(self.0).to_hex().to_string()
    }
}

impl std::fmt::Debug for ArtifactKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ArtifactKey({})", self.to_hex())
    }
}

/// Collects the inputs of an artifact into its key. Start one with
/// `Store::key`, which contributes the compiler version and the artifact
/// kind.
///
/// Every input is hashed with its length, so the key depends on where one
/// input ends and the next begins: `"ab", "c"` and `"a", "bc"` differ.
pub struct KeyBuilder {
    hasher: blake3::Hasher,
}

impl KeyBuilder {
    fn new(version: &str, kind: &str) -> KeyBuilder {
        KeyBuilder {
            hasher: blake3::Hasher::new(),
        }
        .str(version)
        .str(kind)
    }

    pub fn bytes(mut self, input: &[u8]) -> KeyBuilder {
        self.hasher.update(&(input.len() as u64).to_le_bytes());
        self.hasher.update(input);
        self
    }

    pub fn str(self, input: &str) -> KeyBuilder {
        self.bytes(input.as_bytes())
    }

    pub fn u64(self, input: u64) -> KeyBuilder {
        self.bytes(&input.to_le_bytes())
    }

    /// Another artifact as an input, by its key: the key already stands for
    /// everything that artifact depends on.
    pub fn key(self, input: &ArtifactKey) -> KeyBuilder {
        self.bytes(&input.0)
    }

    pub fn finish(self) -> ArtifactKey {
        ArtifactKey(*self.hasher.finalize().as_bytes())
    }
}

/// A directory of artifacts. Several stores, in one process or in many, may
/// use the same directory at once.
pub struct Store {
    dir: PathBuf,
    /// Part of every key, so artifacts of another compiler build are never
    /// found.
    version: String,
}

/// Makes temporary file names unique within the process.
static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

impl Store {
    /// Opens the store in `dir`, creating the directory if needed. `version`
    /// identifies the compiler build.
    pub fn open(dir: impl Into<PathBuf>, version: impl Into<String>) -> io::Result<Store> {
        let dir = dir.into();
        fs::create_dir_all(dir.join("tmp"))?;
        Ok(Store {
            dir,
            version: version.into(),
        })
    }

    pub fn dir(&self) -> &Path {
        &self.dir
    }

    /// Starts the key of an artifact of the given kind, such as `"mir"`.
    pub fn key(&self, kind: &str) -> KeyBuilder {
        KeyBuilder::new(&self.version, kind)
    }

    fn path(&self, key: ArtifactKey) -> PathBuf {
        let hex = key.to_hex();
        self.dir.join(&hex[..2]).join(&hex[2..])
    }

    /// Stores an artifact. Storing under a key that exists replaces the
    /// file, which changes nothing, because a key determines its content.
    pub fn put(&self, key: ArtifactKey, bytes: &[u8]) -> io::Result<()> {
        let temp = self.dir.join("tmp").join(format!(
            "{}-{}",
            std::process::id(),
            NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
        ));
        let written = (|| {
            let mut file = fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&temp)?;
            file.write_all(blake3::hash(bytes).as_bytes())?;
            file.write_all(bytes)?;
            drop(file);
            let path = self.path(key);
            fs::create_dir_all(path.parent().expect("an artifact path has a parent"))?;
            fs::rename(&temp, &path)
        })();
        if written.is_err() {
            let _ = fs::remove_file(&temp);
        }
        written
    }

    /// Loads an artifact, or returns `None` if there is none. A file that is
    /// incomplete or damaged counts as none and is removed.
    pub fn get(&self, key: ArtifactKey) -> io::Result<Option<Vec<u8>>> {
        let path = self.path(key);
        let mut data = match fs::read(&path) {
            Ok(data) => data,
            Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(e) => return Err(e),
        };
        let intact = data.len() >= HASH_BYTES
            && blake3::hash(&data[HASH_BYTES..]).as_bytes()[..] == data[..HASH_BYTES];
        if !intact {
            // Another process may have replaced the file meanwhile; removing
            // a good copy only costs a recompilation.
            let _ = fs::remove_file(&path);
            return Ok(None);
        }
        data.drain(..HASH_BYTES);
        Ok(Some(data))
    }
}

/// How a process holds the store's lock.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LockMode {
    /// For building: several processes at once.
    Shared,
    /// For garbage collection: no one else.
    Exclusive,
}

/// The store's lock, held until it is dropped.
pub struct StoreGuard {
    _file: fs::File,
}

/// What a garbage collection did.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct GcReport {
    pub kept: usize,
    pub removed: usize,
    /// The roots of projects that no longer exist, removed.
    pub stale_roots: usize,
}

impl Store {
    /// Takes the store's lock, waiting for it.
    pub fn lock(&self, mode: LockMode) -> io::Result<StoreGuard> {
        self.take_lock(mode, true)
            .map(|guard| guard.expect("a blocking lock is taken"))
    }

    /// Takes the store's lock if no other process holds it in a way that
    /// excludes `mode`.
    pub fn try_lock(&self, mode: LockMode) -> io::Result<Option<StoreGuard>> {
        self.take_lock(mode, false)
    }

    fn take_lock(&self, mode: LockMode, wait: bool) -> io::Result<Option<StoreGuard>> {
        let file = fs::OpenOptions::new()
            .create(true)
            .truncate(false)
            .write(true)
            .open(self.dir.join("lock"))?;
        #[cfg(unix)]
        {
            use std::os::fd::AsRawFd;
            let mut op = match mode {
                LockMode::Shared => libc::LOCK_SH,
                LockMode::Exclusive => libc::LOCK_EX,
            };
            if !wait {
                op |= libc::LOCK_NB;
            }
            // SAFETY: flock on a descriptor this function owns.
            if unsafe { libc::flock(file.as_raw_fd(), op) } != 0 {
                let error = io::Error::last_os_error();
                if error.kind() == io::ErrorKind::WouldBlock {
                    return Ok(None);
                }
                return Err(error);
            }
        }
        #[cfg(not(unix))]
        let _ = (mode, wait);
        Ok(Some(StoreGuard { _file: file }))
    }

    fn roots_file(&self, project: &Path) -> PathBuf {
        let name = blake3::hash(project.to_string_lossy().as_bytes()).to_hex();
        self.dir.join("roots").join(&name[..32])
    }

    /// Records the artifacts a project's builds use, replacing what was
    /// recorded for it before. `project` is its root, made absolute.
    pub fn set_roots(&self, project: &Path, keys: &[ArtifactKey]) -> io::Result<()> {
        fs::create_dir_all(self.dir.join("roots"))?;
        let mut text = format!("{}\n", project.display());
        let mut hexes: Vec<String> = keys.iter().map(ArtifactKey::to_hex).collect();
        hexes.sort();
        hexes.dedup();
        for hex in hexes {
            text.push_str(&hex);
            text.push('\n');
        }
        let temp = self.dir.join("tmp").join(format!(
            "roots-{}-{}",
            std::process::id(),
            NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
        ));
        fs::write(&temp, text)?;
        fs::rename(&temp, self.roots_file(project))
    }

    /// Removes the artifacts no project's roots name and that are older
    /// than `min_age`, and the roots of projects that no longer exist: a
    /// directory without `package.crag`. The caller holds the exclusive
    /// lock.
    pub fn collect_garbage(&self, min_age: Duration) -> io::Result<GcReport> {
        let mut report = GcReport::default();
        let mut live: HashSet<String> = HashSet::new();
        if let Ok(entries) = fs::read_dir(self.dir.join("roots")) {
            for entry in entries.flatten() {
                let text = fs::read_to_string(entry.path()).unwrap_or_default();
                let mut lines = text.lines();
                let project = lines.next().unwrap_or_default();
                if !Path::new(project).join("package.crag").is_file() {
                    fs::remove_file(entry.path())?;
                    report.stale_roots += 1;
                    continue;
                }
                live.extend(lines.map(str::to_string));
            }
        }
        let now = SystemTime::now();
        let old = |path: &Path| {
            fs::metadata(path)
                .and_then(|m| m.modified())
                .map(|t| now.duration_since(t).unwrap_or_default() >= min_age)
                .unwrap_or(false)
        };
        for entry in fs::read_dir(&self.dir)?.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            let path = entry.path();
            if name == "tmp" {
                for temp in fs::read_dir(&path)?.flatten() {
                    if old(&temp.path()) {
                        let _ = fs::remove_file(temp.path());
                    }
                }
                continue;
            }
            if name.len() != 2 || !path.is_dir() {
                continue;
            }
            for file in fs::read_dir(&path)?.flatten() {
                let hex = format!("{name}{}", file.file_name().to_string_lossy());
                if live.contains(&hex) || !old(&file.path()) {
                    report.kept += 1;
                } else {
                    fs::remove_file(file.path())?;
                    report.removed += 1;
                }
            }
        }
        Ok(report)
    }
}
