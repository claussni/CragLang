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
//! ```
//!
//! A file holds the BLAKE3 hash of the payload, then the payload. Writers
//! fill a temporary file and rename it into place. Renaming is atomic, so a
//! reader in this or another process sees either no file or a whole one.
//! The store does not force data to disk, since losing an artifact costs
//! only a recompilation; the hash catches a file a crash left incomplete,
//! and `get` then reports the artifact as missing.

use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

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
