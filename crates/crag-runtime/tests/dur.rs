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

//! A durable counter survives the process (Plan §11.11.4, Chapter 12):
//! `dur hits = 0`, incremented through the commit pipeline, killed at
//! random points, keeps a consistent, monotonic value, and a clean run
//! ends at exactly its start plus its increments. The full harness with
//! a thousand kills and fault injection is 11.11.11; this is the exit of
//! the pipeline step.
//!
//! The test runs itself as the child: with `CRAG_DUR_CHILD` set it opens
//! the store named there, prints `start <n>`, increments, and prints
//! `end <n>` when it finishes before the parent kills it.

use std::io::{BufRead, BufReader};
use std::process::{Child, Command, Stdio};
use std::sync::Arc;
use std::time::{Duration, Instant};

use crag_dur::lmdb::LmdbStore;
use crag_dur::{Durability, NodeStore};
use crag_runtime::dur::DurStore;

/// Increments per child run; the kill usually comes in their middle.
const INCREMENTS: u64 = 50;

/// The child: opens the store, counts, reports.
fn child(path: &str) {
    let backend = LmdbStore::open(path.as_ref(), 10 << 20, Durability::Full).unwrap();
    let store = DurStore::new(backend as Arc<dyn NodeStore>);
    let hits = store.slot_words(b"hits", [0, 0]).unwrap();
    println!("start {}", hits.get()[0]);
    for _ in 0..INCREMENTS {
        hits.update(|[n, _]| [n + 1, 0]).unwrap();
    }
    println!("end {}", hits.get()[0]);
}

/// Runs this test again as the child and gives its handle.
fn spawn_child(path: &std::path::Path) -> Child {
    Command::new(std::env::current_exe().unwrap())
        .args(["a_counter_survives_kills", "--exact", "--nocapture"])
        .env("CRAG_DUR_CHILD", path)
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .unwrap()
}

/// The number after `word` on the child's next matching line, within
/// `wait`; the child is killed and the test fails when none comes.
fn number(lines: &mut impl Iterator<Item = std::io::Result<String>>, word: &str) -> u64 {
    for line in lines {
        let line = line.expect("the child's output ends only with it");
        if let Some(rest) = line.strip_prefix(word) {
            return rest.trim().parse().expect("a count after the word");
        }
    }
    panic!("the child ended without printing `{word}`");
}

/// Waits for the child, bounded, so no run hangs.
fn wait_bounded(child: &mut Child, limit: Duration) {
    let from = Instant::now();
    loop {
        if child.try_wait().unwrap().is_some() {
            return;
        }
        if from.elapsed() > limit {
            let _ = child.kill();
            let _ = child.wait();
            panic!("the child ran past {limit:?}");
        }
        std::thread::sleep(Duration::from_millis(5));
    }
}

#[test]
fn a_counter_survives_kills() {
    if let Ok(path) = std::env::var("CRAG_DUR_CHILD") {
        child(&path);
        return;
    }
    let dir = std::env::temp_dir().join(format!("crag-dur-kill-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("hits.crag");

    // Rounds that die at random points of the commit loop: the stored
    // count only ever grows, and every restart opens the store and reads
    // a value.
    let mut seen = 0;
    let mut rng = 0x9e37_79b9_7f4a_7c15u64 | std::process::id() as u64;
    for _ in 0..8 {
        let mut run = spawn_child(&path);
        let mut lines = BufReader::new(run.stdout.take().unwrap()).lines();
        let start = number(&mut lines, "start ");
        assert!(
            start >= seen,
            "the counter went back from {seen} to {start} over a kill"
        );
        assert!(start <= seen + INCREMENTS, "more increments than ran");
        seen = start;
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        std::thread::sleep(Duration::from_millis(rng % 25));
        let _ = run.kill();
        let _ = run.wait();
    }

    // A clean run: it ends at its start plus its increments, and the
    // next open reads exactly that.
    let mut run = spawn_child(&path);
    let mut lines = BufReader::new(run.stdout.take().unwrap()).lines();
    let start = number(&mut lines, "start ");
    assert!(start >= seen);
    let end = number(&mut lines, "end ");
    assert_eq!(end, start + INCREMENTS);
    wait_bounded(&mut run, Duration::from_secs(30));

    let backend = LmdbStore::open(&path, 10 << 20, Durability::Full).unwrap();
    let store = DurStore::new(backend as Arc<dyn NodeStore>);
    let hits = store.slot_words(b"hits", [0, 0]).unwrap();
    assert_eq!(
        hits.get(),
        [end, 0],
        "the clean run's count did not survive the restart"
    );
    drop((hits, store));
    let _ = std::fs::remove_dir_all(&dir);
}
