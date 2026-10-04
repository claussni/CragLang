//! Uses the facade the way the compiler crates will: as a separate crate
//! that never names Salsa, except in the one line the macros require.

extern crate crag_db as salsa;

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use crag_db::{Db, Durability, RootDatabase, Setter, catch_cancelled, check_cancelled};

#[crag_db::input]
struct SourceFile {
    #[returns(ref)]
    text: String,
}

#[crag_db::interned(debug)]
struct Name<'db> {
    #[returns(ref)]
    text: String,
}

/// A plain type as a query result.
#[derive(Clone, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
struct Summary {
    lines: usize,
}

static SUMMARIZE_RUNS: AtomicUsize = AtomicUsize::new(0);
static IS_LONG_RUNS: AtomicUsize = AtomicUsize::new(0);

#[crag_db::tracked]
fn summarize(db: &dyn Db, file: SourceFile) -> Summary {
    SUMMARIZE_RUNS.fetch_add(1, Ordering::Relaxed);
    Summary {
        lines: file.text(db).lines().count(),
    }
}

#[crag_db::tracked]
fn is_long(db: &dyn Db, file: SourceFile) -> bool {
    IS_LONG_RUNS.fetch_add(1, Ordering::Relaxed);
    summarize(db, file).lines > 2
}

#[test]
fn results_are_cached_and_unchanged_results_stop_recomputation() {
    let mut db = RootDatabase::new();
    let file = SourceFile::new(&db, "a\nb".to_string());
    let runs = || {
        (
            SUMMARIZE_RUNS.load(Ordering::Relaxed),
            IS_LONG_RUNS.load(Ordering::Relaxed),
        )
    };

    assert!(!is_long(&db, file));
    assert_eq!(runs(), (1, 1));

    // Asked again: both answers come from the cache.
    assert!(!is_long(&db, file));
    assert_eq!(runs(), (1, 1));

    // Other text, same number of lines: the summary is recomputed and comes
    // out equal, so the query that depends on it is not rerun.
    file.set_text(&mut db).to("c\nd".to_string());
    assert!(!is_long(&db, file));
    assert_eq!(runs(), (2, 1));

    // More lines: now both rerun.
    file.set_text(&mut db).to("c\nd\ne".to_string());
    assert!(is_long(&db, file));
    assert_eq!(runs(), (3, 2));
}

#[test]
fn equal_values_intern_to_the_same_id() {
    let db = RootDatabase::new();
    let first = Name::new(&db, "main".to_string());
    let again = Name::new(&db, "main".to_string());
    let other = Name::new(&db, "helper".to_string());
    assert_eq!(first, again);
    assert_ne!(first, other);
    assert_eq!(first.text(&db), "main");
}

#[test]
fn inputs_take_a_durability() {
    let mut db = RootDatabase::new();
    let library = SourceFile::new(&db, "std".to_string());
    library
        .set_text(&mut db)
        .with_durability(Durability::HIGH)
        .to("std v2".to_string());
    assert_eq!(library.text(&db), "std v2");
}

static SPINNING: AtomicBool = AtomicBool::new(false);

/// A query that never finishes by itself.
#[crag_db::tracked]
fn spin(db: &dyn Db, file: SourceFile) -> usize {
    let _ = file.text(db);
    SPINNING.store(true, Ordering::SeqCst);
    loop {
        check_cancelled(db);
        std::thread::yield_now();
    }
}

#[test]
fn changing_an_input_cancels_queries_on_snapshots() {
    let mut db = RootDatabase::new();
    let file = SourceFile::new(&db, "old".to_string());

    let snapshot = db.snapshot();
    let reader = std::thread::spawn(move || {
        // The snapshot is dropped when this closure ends, which is what lets
        // the change below go ahead.
        let db = snapshot.db();
        let seen_before: String = db.text_of(file);
        // A query returns a reference into the database; copy the result out
        // so it does not borrow the snapshot.
        let outcome = catch_cancelled(|| *spin(db, file));
        (seen_before, outcome)
    });

    while !SPINNING.load(Ordering::SeqCst) {
        std::thread::yield_now();
    }
    // Blocks until the reader has stopped and dropped its snapshot.
    file.set_text(&mut db).to("new".to_string());

    let (seen_before, outcome) = reader.join().unwrap();
    assert_eq!(seen_before, "old");
    assert_eq!(outcome, Err(crag_db::Cancelled));
    assert_eq!(file.text(&db), "new");
}

/// Reads through `&dyn Db`, as code outside queries does.
trait TextOf {
    fn text_of(&self, file: SourceFile) -> String;
}

impl TextOf for dyn Db + '_ {
    fn text_of(&self, file: SourceFile) -> String {
        file.text(self).clone()
    }
}
