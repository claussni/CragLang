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

//! End-to-end tests of the concurrency features (Plan §11.7.14): Crag
//! projects compiled and run on the scheduler. A watchdog ends the process
//! if a test hangs.

use std::fs;
use std::path::PathBuf;
use std::sync::Once;
use std::time::{Duration, Instant};

use crag_driver::crag_run;

/// Ends the test process if the tests take longer than a minute.
fn watchdog() {
    static START: Once = Once::new();
    START.call_once(|| {
        std::thread::spawn(|| {
            std::thread::sleep(Duration::from_secs(60));
            eprintln!("the concurrency tests hung");
            std::process::abort();
        });
    });
}

fn project(name: &str, app: &str) -> PathBuf {
    let root = std::env::temp_dir().join(format!("crag-conc-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("package.crag"),
        "package demo 0.1\nruntime 0.0\nmain demo.app\n",
    )
    .unwrap();
    fs::write(root.join("app.crag"), app).unwrap();
    root
}

/// Runs the project's `main`: its exit status and what it printed.
fn run(name: &str, app: &str) -> (u8, String) {
    watchdog();
    let root = project(name, app);
    let mut out = Vec::new();
    let code = crag_run(&root, &mut out);
    let _ = fs::remove_dir_all(&root);
    (code, String::from_utf8(out).unwrap())
}

#[test]
fn sleep_suspends_the_task() {
    let start = Instant::now();
    let (code, out) = run(
        "sleep",
        "import std.time\n\nfn main() -> ExitCode {\n  sleep(millis(50))\n  sleep(nanos(-1))\n  ExitCode(code: 3)\n}\n",
    );
    assert_eq!(code, 3, "{out}");
    assert!(start.elapsed() >= Duration::from_millis(50));
}

#[test]
fn refs_read_update_and_swap() {
    let (code, out) = run(
        "refs",
        r#"fn main() -> ExitCode {
  ref hits = 40
  hits.update { n -> n + 1 }
  let x = hits.use()
  let old = hits.swap(x + 1)
  ExitCode(code: hits.use { n -> n + old - 41 })
}
"#,
    );
    assert_eq!(code, 42, "{out}");
}

#[test]
fn a_ref_holds_counted_values() {
    let (code, out) = run(
        "ref-text",
        r#"fn main() -> ExitCode {
  ref s = "ab"
  s.update { t -> "{t} and a string too long to be inline" }
  let t = s.use()
  s.update { t -> t }
  if s.use() == "ab and a string too long to be inline" and t == s.use() {
    ExitCode(code: 1)
  } else {
    ExitCode(code: 2)
  }
}
"#,
    );
    assert_eq!(code, 1, "{out}");
}

#[test]
fn an_update_that_gives_an_error_writes_nothing() {
    let (code, out) = run(
        "ref-error",
        r#"type TooBig(..Error)

fn bump(r: Ref[Int]) -> () | TooBig {
  r.update { n -> if n > 1 { TooBig } else { n + 1 } }
}

fn main() -> ExitCode {
  ref n = 0
  let a = bump(n)
  let b = bump(n)
  let c = bump(n)
  case c {
    TooBig -> ExitCode(code: n.use() + 10)
    _ -> ExitCode(code: 0)
  }
}
"#,
    );
    assert_eq!(code, 12, "{out}");
}

#[test]
fn empty_takes_the_value_out() {
    let (code, out) = run(
        "ref-empty",
        r#"fn main() -> ExitCode {
  ref slot: Option[Int] = 7
  let first = slot.empty()
  let second = slot.empty()
  case first {
    n: Int -> case second {
      Empty -> ExitCode(code: n)
      _ -> ExitCode(code: 1)
    }
    _ -> ExitCode(code: 2)
  }
}
"#,
    );
    assert_eq!(code, 7, "{out}");
}

#[test]
fn a_commutative_update_applies_in_the_cell() {
    let (code, out) = run(
        "ref-apply",
        r#"fn main() -> ExitCode {
  ref n = 1
  let k = 3
  n.update { v -> v + k }
  n.update { v -> 2 * v }
  n.update { v -> v - 1 }
  ExitCode(code: n.use())
}
"#,
    );
    assert_eq!(code, 7, "{out}");
}

#[test]
fn a_commutative_update_traps_on_overflow() {
    let (code, out) = run(
        "ref-apply-overflow",
        r#"fn main() -> ExitCode {
  ref n: UInt8 = 250
  n.update { v -> v + 10 }
  ExitCode(code: 0)
}
"#,
    );
    assert_eq!(code, 70, "{out}");
    assert!(out.starts_with("trap: arithmetic overflow"), "{out}");
}
