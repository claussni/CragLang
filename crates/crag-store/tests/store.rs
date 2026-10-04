use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU32, Ordering};

use crag_store::{ArtifactKey, Store};

/// A fresh directory under the system's temporary directory, removed on drop.
struct TempDir(PathBuf);

impl TempDir {
    fn new() -> TempDir {
        static NEXT: AtomicU32 = AtomicU32::new(0);
        let name = format!(
            "crag-store-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        );
        TempDir(std::env::temp_dir().join(name))
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn artifact_file(store: &Store, key: ArtifactKey) -> PathBuf {
    let hex = key.to_hex();
    store.dir().join(&hex[..2]).join(&hex[2..])
}

fn temp_files(store: &Store) -> usize {
    fs::read_dir(store.dir().join("tmp")).unwrap().count()
}

#[test]
fn an_artifact_comes_back_as_stored() {
    let dir = TempDir::new();
    let store = Store::open(&dir.0, "v1").unwrap();
    let key = store.key("mir").str("fn main").finish();

    assert_eq!(store.get(key).unwrap(), None);
    store.put(key, b"some mir").unwrap();
    assert_eq!(store.get(key).unwrap().as_deref(), Some(&b"some mir"[..]));

    // An empty artifact is still an artifact.
    let empty = store.key("mir").str("fn empty").finish();
    store.put(empty, b"").unwrap();
    assert_eq!(store.get(empty).unwrap().as_deref(), Some(&b""[..]));

    // Nothing is left in the temporary directory, and the file is named by
    // the key.
    assert_eq!(temp_files(&store), 0);
    assert!(artifact_file(&store, key).is_file());
}

#[test]
fn artifacts_survive_reopening_the_store() {
    let dir = TempDir::new();
    let key = {
        let store = Store::open(&dir.0, "v1").unwrap();
        let key = store.key("code").u64(7).finish();
        store.put(key, b"machine code").unwrap();
        key
    };
    let store = Store::open(&dir.0, "v1").unwrap();
    assert_eq!(store.key("code").u64(7).finish(), key);
    assert_eq!(
        store.get(key).unwrap().as_deref(),
        Some(&b"machine code"[..])
    );
}

#[test]
fn a_key_depends_on_every_input() {
    let dir = TempDir::new();
    let store = Store::open(&dir.0, "v1").unwrap();
    let other_version = Store::open(&dir.0, "v2").unwrap();

    let base = store.key("mir").str("ab").str("c").finish();
    let same = store.key("mir").str("ab").str("c").finish();
    assert_eq!(base, same);

    let variants = [
        other_version.key("mir").str("ab").str("c").finish(), // compiler version
        store.key("code").str("ab").str("c").finish(),        // kind
        store.key("mir").str("ab").str("d").finish(),         // an input's content
        store.key("mir").str("a").str("bc").finish(),         // where inputs divide
        store.key("mir").str("ab").str("c").str("").finish(), // number of inputs
        store.key("mir").str("ab").str("c").key(&base).finish(), // another artifact
    ];
    for (i, key) in variants.iter().enumerate() {
        assert_ne!(*key, base, "variant {i}");
        for other in &variants[..i] {
            assert_ne!(key, other);
        }
    }

    // A compiler of another version does not find this one's artifacts.
    store.put(base, b"old").unwrap();
    assert_eq!(other_version.get(variants[0]).unwrap(), None);
}

#[test]
fn a_damaged_file_counts_as_missing_and_is_removed() {
    let dir = TempDir::new();
    let store = Store::open(&dir.0, "v1").unwrap();
    type Damage = fn(&mut Vec<u8>);
    let damage: [(&str, Damage); 4] = [
        ("payload changed", |data| *data.last_mut().unwrap() ^= 1),
        ("payload cut short", |data| data.truncate(data.len() - 3)),
        ("cut inside the hash", |data| data.truncate(10)),
        ("empty file", |data| data.clear()),
    ];
    for (what, apply) in damage {
        let key = store.key("mir").str(what).finish();
        store.put(key, b"a payload").unwrap();
        let path = artifact_file(&store, key);
        let mut data = fs::read(&path).unwrap();
        apply(&mut data);
        fs::write(&path, data).unwrap();

        assert_eq!(store.get(key).unwrap(), None, "{what}");
        assert!(!path.exists(), "{what}");

        // Storing again repairs it.
        store.put(key, b"a payload").unwrap();
        assert_eq!(store.get(key).unwrap().as_deref(), Some(&b"a payload"[..]));
    }
}

#[test]
fn concurrent_writers_and_readers_see_only_whole_artifacts() {
    let dir = TempDir::new();
    let payload = vec![0xabu8; 1 << 16];
    let key = Store::open(&dir.0, "v1")
        .unwrap()
        .key("code")
        .str("shared")
        .finish();

    std::thread::scope(|scope| {
        for _ in 0..4 {
            scope.spawn(|| {
                // Each thread has its own store on the same directory, as
                // separate processes would.
                let store = Store::open(&dir.0, "v1").unwrap();
                for _ in 0..50 {
                    store.put(key, &payload).unwrap();
                    if let Some(found) = store.get(key).unwrap() {
                        assert_eq!(found, payload);
                    }
                }
            });
        }
    });

    let store = Store::open(&dir.0, "v1").unwrap();
    assert_eq!(store.get(key).unwrap().as_deref(), Some(&payload[..]));
    assert_eq!(temp_files(&store), 0);
}
