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

use crag_driver::{EXIT_TRAP, crag_run};

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

#[test]
fn an_atomic_block_commits_its_updates_together() {
    let (code, out) = run(
        "atomic",
        r#"fn move(from: Ref[Int], to: Ref[Int], amount: Int) -> () {
  from.update { b -> b - amount }
  to.update { b -> b + amount }
}

fn main() -> ExitCode {
  ref a = 100
  ref b = 0
  atomic {
    a.update { x -> x - 25 }
    b.update { x -> x + 25 }
  }
  atomic { move(a, b, 5) }
  let both = atomic { a.use() * 1000 + b.use() }
  ExitCode(code: both % 256)
}
"#,
    );
    // 70 * 1000 + 30 = 70030, and 70030 % 256 = 142.
    assert_eq!(code, 142, "{out}");
}

#[test]
fn an_atomic_block_with_an_error_value_writes_nothing() {
    let (code, out) = run(
        "atomic-abort",
        r#"type InsufficientFunds(..Error)

fn transfer(from: Ref[Int], to: Ref[Int], amount: Int) -> () | InsufficientFunds {
  atomic {
    to.update { b -> b + amount }
    if from.use() < amount { return InsufficientFunds }
    from.update { b -> b - amount }
  }
}

fn main() -> ExitCode {
  ref a = 10
  ref b = 0
  let first = transfer(a, b, 4)
  let second = transfer(a, b, 7)
  case second {
    InsufficientFunds -> ExitCode(code: a.use() * 10 + b.use())
    _ -> ExitCode(code: 0)
  }
}
"#,
    );
    assert_eq!(code, 64, "{out}");
}

#[test]
fn nested_atomic_blocks_keep_the_inner_writes() {
    let (code, out) = run(
        "atomic-nested",
        r#"type Nope(..Error)

fn main() -> ExitCode {
  ref n = 1
  atomic {
    n.update { v -> v + 1 }
    let inner = atomic {
      n.update { v -> v * 100 }
      Nope
    }
    atomic { n.update { v -> v * 10 } }
  }
  ExitCode(code: n.use())
}
"#,
    );
    assert_eq!(code, 20, "{out}");
}

#[test]
fn a_group_runs_its_tasks_before_it_returns() {
    let (code, out) = run(
        "group",
        r#"import std.task

fn main() -> ExitCode {
  ref hits = 0
  let n = all(limit: 3) { g ->
    for i in 1..20 {
      g.start { -> hits.update { h -> h + i } }
    }
    7
  }
  ExitCode(code: hits.use() - 200 + n)
}
"#,
    );
    // 1 + 2 + ... + 20 = 210.
    assert_eq!(code, 17, "{out}");
}

#[test]
fn refs_of_flat_values_keep_every_update_under_contention() {
    let (code, out) = run(
        "flat-refs",
        r#"import std.task

type Tally(sum: Int, odd: Bool)
type Named(text: Str)

fn main() -> ExitCode {
  ref p = Tally(sum: 0, odd: False)
  ref name = Named(text: "a name long enough for a heap buffer ")
  all(limit: 8) { g ->
    for i in 1..40 {
      g.start { ->
        p.update { v -> Tally(sum: v.sum + i, odd: if v.odd { False } else { True }) }
        name.update { v -> Named(text: "{v.text}x") }
      }
    }
    0
  }
  atomic {
    p.update { v -> Tally(sum: v.sum + 1, odd: if v.odd { False } else { True }) }
    name.update { v -> Named(text: "{v.text}!") }
  }
  let v = p.use()
  let tally = if v.sum == 821 and v.odd { 0 } else { 1 }
  let names = if name.use().text == "a name long enough for a heap buffer xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx!" { 0 } else { 2 }
  ExitCode(code: tally + names)
}
"#,
    );
    // 1 + 2 + ... + 40 = 820, and 41 flips of `odd`.
    assert_eq!(code, 0, "{out}");
}

#[test]
fn first_result_takes_the_first_value_a_task_gives() {
    let (code, out) = run(
        "first-result",
        r#"import std.task
import std.time

fn main() -> ExitCode {
  let found: Option[Int] = firstResult { g ->
    g.start { -> Empty }
    g.start { -> sleep(millis(5))
      42 }
    g.start { -> sleep(seconds(30))
      1 }
  }
  case found {
    n: Int -> ExitCode(code: n)
    _ -> ExitCode(code: 0)
  }
}
"#,
    );
    assert_eq!(code, 42, "{out}");
}

#[test]
fn transactions_keep_their_invariant_under_contention() {
    for round in 0..3 {
        let (code, out) = run(
            &format!("contention-{round}"),
            r#"import std.task

fn transfer(from: Ref[Int], to: Ref[Int], amount: Int) -> () {
  from.update { b -> b - amount }
  to.update { b -> b + amount }
}

fn main() -> ExitCode {
  ref a = 1000
  ref b = 1000
  ref bad = 0
  ref bumps = 0
  all(limit: 32) { g ->
    for i in 1..200 {
      g.start { -> atomic { transfer(a, b, 3) } }
      g.start { -> atomic { transfer(b, a, 2) } }
      g.start { -> atomic {
        if a.use() + b.use() != 2000 { bad.update { n -> n + 1 } }
      } }
      g.start { -> bumps.update { n -> if n >= 0 { n + 1 } else { n } } }
    }
  }
  if bad.use() == 0 and a.use() == 800 and b.use() == 1200 and bumps.use() == 200 {
    ExitCode(code: 0)
  } else {
    ExitCode(code: 1)
  }
}
"#,
        );
        assert_eq!(code, 0, "{out}");
    }
}

#[test]
fn ext_runs_each_closure_once_under_its_lock() {
    let (code, out) = run(
        "ext",
        r#"import std.task

fn main() -> ExitCode {
  ext log = ""
  ext n = 0
  all(limit: 8) { g ->
    for i in 1..50 {
      g.start { -> n.update { v -> v + 1 } }
    }
  }
  log.update { s -> "{s} and a text too long to be inline" }
  let old = log.swap("short")
  let k = n.use { v -> v * 2 }
  if old == " and a text too long to be inline" and log.use() == "short" {
    ExitCode(code: k - n.use())
  } else {
    ExitCode(code: 1)
  }
}
"#,
    );
    assert_eq!(code, 50, "{out}");
}

#[test]
fn a_lazy_value_is_computed_once() {
    let (code, out) = run(
        "lazy",
        r#"import std.task
import std.time

fn main() -> ExitCode {
  ref runs = 0
  let text = lazy {
    runs.update { n -> n + 1 }
    sleep(millis(10))
    "computed once by its first reader"
  }
  ref same = 0
  all { g ->
    for i in 1..20 {
      g.start { ->
        if text.value == "computed once by its first reader" {
          same.update { n -> n + 1 }
        }
      }
    }
  }
  ExitCode(code: runs.use() * 100 + same.use())
}
"#,
    );
    assert_eq!(code, 120, "{out}");
}

#[test]
fn a_lazy_value_that_traps_traps_its_readers() {
    let (code, out) = run(
        "lazy-trap",
        r#"fn main() -> ExitCode {
  let n = 0
  let bad = lazy 10 / n
  ExitCode(code: bad.value)
}
"#,
    );
    assert_eq!(code, 70, "{out}");
    assert!(out.starts_with("trap: division by zero"), "{out}");
}

#[test]
fn a_stream_carries_values_from_a_producer_to_a_consumer() {
    let (code, out) = run(
        "stream",
        r#"import std.stream
import std.task

fn main() -> ExitCode {
  let ends = stream[Str](capacity: 2)
  let sink = ends.sink
  let source = ends.source
  ref total = 0
  all { g ->
    g.start { -> sink.putAll(["a", "a string too long to be inline", "bc"]) }
    g.start { ->
      for s in source {
        if s == "a string too long to be inline" {
          total.update { n -> n + 30 }
        } else {
          total.update { n -> n + 1 }
        }
      }
    }
  }
  ExitCode(code: total.use())
}
"#,
    );
    assert_eq!(code, 32, "{out}");
}

#[test]
fn a_consumer_reads_abandoned_when_the_producer_goes_without_closing() {
    let (code, out) = run(
        "stream-abandoned",
        r#"import std.stream
import std.task

fn main() -> ExitCode {
  let ends = infiniteStream[Int](capacity: 0)
  let sink = ends.sink
  let source = ends.source
  ref seen = 0
  all { g ->
    g.start { -> let sent = sink.put(7) }
    g.start { ->
      let first = source.next()
      let second = source.next()
      let k = case first {
        n: Int -> case second {
          Abandoned -> n
          _ -> 1
        }
        _ -> 2
      }
      seen.update { _ -> k }
    }
  }
  ExitCode(code: seen.use())
}
"#,
    );
    assert_eq!(code, 7, "{out}");
}

#[test]
fn a_fan_out_hub_hands_each_value_to_one_worker() {
    let (code, out) = run(
        "hub",
        r#"import std.stream
import std.task

fn main() -> ExitCode {
  let jobs = fanOut[Int](capacity: 4)
  ref sum = 0
  all { g ->
    let feed = jobs.sink()
    g.start { -> feed.putAll([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) }
    jobs.seal()
    for w in 1..3 {
      let src = jobs.source()
      g.start { -> for job in src { sum.update { n -> n + job } } }
    }
  }
  ExitCode(code: sum.use())
}
"#,
    );
    assert_eq!(code, 55, "{out}");
}

/// The M4 exit example (Plan §6): a server that serves its connections
/// from a task group, each in a task of its own, echoing what it reads.
const ECHO_SERVER: &str = r#"import std.io
import std.task

fn serve(c: Connection) -> () {
  case c.read() {
    bytes: Bytes -> {
      let written = c.write(bytes)
      serve(c)
    }
    _ -> ()
  }
}

fn main() -> ExitCode {
  case listen(PORT) {
    l: Listener -> {
      all(limit: 64) { g ->
        for i in 1..CONNECTIONS {
          case l.accept() {
            c: Connection -> g.start { -> serve(c) }
            _ -> ()
          }
        }
      }
      ExitCode(code: 0)
    }
    _ -> ExitCode(code: 1)
  }
}
"#;

/// Runs the echo server for `connections` clients, each sending
/// `messages` messages of growing length, and checks every echo.
fn echo(name: &str, connections: usize, messages: usize) {
    use std::io::{Read, Write};
    use std::net::{TcpListener, TcpStream};

    let port = TcpListener::bind("127.0.0.1:0")
        .unwrap()
        .local_addr()
        .unwrap()
        .port();
    let app = ECHO_SERVER
        .replace("PORT", &port.to_string())
        .replace("CONNECTIONS", &connections.to_string());
    let server = std::thread::spawn({
        let name = name.to_string();
        move || run(&name, &app)
    });
    let clients: Vec<_> = (0..connections)
        .map(|k| {
            std::thread::spawn(move || {
                let mut stream = loop {
                    match TcpStream::connect(("127.0.0.1", port)) {
                        Ok(stream) => break stream,
                        Err(_) => std::thread::sleep(Duration::from_millis(5)),
                    }
                };
                for m in 0..messages {
                    let message = format!("client {k} message {m} {}", "x".repeat(m * 37));
                    stream.write_all(message.as_bytes()).unwrap();
                    let mut echoed = vec![0; message.len()];
                    stream.read_exact(&mut echoed).unwrap();
                    assert_eq!(echoed, message.as_bytes());
                }
            })
        })
        .collect();
    for client in clients {
        client.join().unwrap();
    }
    let (code, out) = server.join().unwrap();
    assert_eq!(code, 0, "{out}");
}

#[test]
fn a_server_echoes_for_many_connections_at_once() {
    echo("echo", 50, 20);
}

#[test]
fn a_server_echoes_for_hundreds_of_connections() {
    echo("echo-many", 200, 5);
}

#[test]
fn large_lists_are_freed_between_fibers() {
    let (code, out) = run(
        "teardown",
        r#"import std.task

type Node(label: Str, children: List[Node])

fn build(depth: Int) -> Node {
  if depth == 0 {
    return Node(label: "a leaf with a label too long to be inline", children: [])
  }
  let c = [build(depth - 1), build(depth - 1), build(depth - 1), build(depth - 1)]
  Node(label: "a node at depth {depth} of the tree", children: c)
}

fn main() -> ExitCode {
  ref built = 0
  all(limit: 4) { g ->
    for i in 1..8 {
      g.start { ->
        let forest = [build(7), build(7)]
        built.update { n -> n + 1 }
      }
    }
  }
  ExitCode(code: built.use())
}
"#,
    );
    assert_eq!(code, 8, "{out}");
}

#[test]
fn signals_reach_the_most_specific_handler_of_the_innermost_block() {
    let (code, out) = run(
        "signals",
        r#"import std.task

pub distinct type ShopSignal(..Signal)
type OrderPlaced(..ShopSignal, total: Int)
type Note(..ShopSignal, n: Int)

fn place(total: Int) -> () {
  emit OrderPlaced(total: total)
}

fn main() -> ExitCode {
  ref orders = 0
  ref shop = 0
  ref outer = 0
  on ShopSignal { s -> outer.update { n -> n + 1 } }
  {
    on ShopSignal { s -> shop.update { n -> n + 1 } }
    on OrderPlaced { o ->
      orders.update { n -> n + o.total }
      // Passes the signal on outward.
      emit o
    }
    place(5)
    emit Note(n: 1)
    all { g ->
      g.start { -> place(7) }
    }
  }
  place(100)
  ExitCode(code: orders.use() * 10 + shop.use() + outer.use())
}
"#,
    );
    // Orders 5 and 7 reach OrderPlaced; each also passes on to the outer
    // ShopSignal handler, the note reaches the inner one, and 100 the
    // outer one after the block: 12 * 10 + 1 + 3.
    assert_eq!(code, 124, "{out}");
}

#[test]
fn signals_of_a_transaction_wait_for_its_outcome() {
    let (code, out) = run(
        "signals-atomic",
        r#"type Failed(..Error)
type Done(..Signal, n: Int)

fn main() -> ExitCode {
  ref seen = 0
  ref a = 0
  on Done { d -> seen.update { s -> s * 10 + d.n } }
  atomic {
    a.update { v -> v + 1 }
    emit ok Done(n: 1)
    emit fail Done(n: 2)
  }
  let r = atomic {
    emit ok Done(n: 3)
    emit fail Done(n: 4)
    Failed
  }
  a.update { v ->
    emit Done(n: 5)
    v + 1
  }
  ExitCode(code: seen.use() % 256)
}
"#,
    );
    // 1, then 4, then 5: 145.
    assert_eq!(code, 145, "{out}");
}

#[test]
fn a_trap_in_a_signal_handler_goes_on_from_the_emit() {
    // §11.3, §8.3.1: a handler runs where the signal is emitted, so a trap
    // in it goes to the trap handlers around the `emit`, in the emitting
    // function or past it, also after an `atomic` block commits; the
    // handler runs again for the next signal.
    let (code, out) = run(
        "signals-trap",
        r#"type Tick(..Signal, n: Int)

fn emitter() -> Int {
  on DivisionByZero { t -> 1 }
  emit Tick(n: 0)
  0
}

fn around() -> Int {
  on Trap { t -> 0 }
  on Tick { s -> let x = 1 / s.n }
  emitter()
}

fn same() -> Int {
  ref seen = 0
  on Tick { s ->
    seen.update { v -> v + 1 }
    let x = 1 / s.n
  }
  let first = {
    on DivisionByZero { t -> 1 }
    emit Tick(n: 0)
    0
  }
  emit Tick(n: 1)
  first * seen.use()
}

fn committed() -> Int {
  on DivisionByZero { t -> 1 }
  on Tick { s -> let x = 1 / s.n }
  atomic {
    emit Tick(n: 0)
  }
  0
}

fn main() -> ExitCode {
  ExitCode(code: around() + 10 * same() + 100 * committed())
}
"#,
    );
    assert_eq!(code, 121, "{out}");
    let (code, out) = run(
        "signals-trap-root",
        r#"type Tick(..Signal, n: Int)

fn main() -> ExitCode {
  on Tick { s -> let x = 1 / s.n }
  emit Tick(n: 0)
  ExitCode(code: 3)
}
"#,
    );
    assert_eq!(code, EXIT_TRAP, "{out}");
    assert!(out.contains("trap: division by zero"), "{out}");
}

#[test]
fn a_signal_no_handler_takes_reaches_the_root() {
    let (code, out) = run(
        "signals-root",
        r#"type Lost(..Signal, n: Int)

fn main() -> ExitCode {
  emit Lost(n: 1)
  ExitCode(code: 3)
}
"#,
    );
    assert_eq!(code, 3, "{out}");
}
