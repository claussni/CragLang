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

//! The eval fuzz run (Implementation Plan §11.12.11): random programs with
//! loops, deep recursion, large allocations and trapping arithmetic go
//! through the agent server's `eval`, and each must end in a structured
//! outcome within the wall budget, never a hung or crashed scratch image.
//! After every program, the session must still answer.
//!
//! `CRAG_FUZZ=200` runs more programs, `CRAG_FUZZ_SEED=7` another
//! sequence; a failure prints the seed and the program to rerun it.

mod common;

use common::client::Client;
use serde_json::{Value, json};

/// xorshift64*: small, seedable and good enough to mix programs.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// A random `Int` expression: literals, arithmetic that may trap or
/// overflow, lists and strings taken back to `Int`, and conditionals.
fn expr(rng: &mut Rng, depth: u32, var: Option<&str>) -> String {
    if depth == 0 {
        return match var {
            Some(name) if rng.below(3) == 0 => name.to_string(),
            _ => format!("{}", rng.below(2000) as i64 - 100),
        };
    }
    let a = expr(rng, depth - 1, var);
    let b = expr(rng, depth - 1, var);
    match rng.below(8) {
        0 => format!("({a} + {b})"),
        1 => format!("({a} - {b})"),
        2 => format!("({a} * {b})"),
        // Trap bait: the divisor can be zero.
        3 => format!("({a} / {b})"),
        4 => format!("[{a}, {b}, {a}].count()"),
        5 => format!("\"{{{a}}}-{{{b}}}\".byteCount()"),
        6 => format!("(if {a} > {b} {{ {a} }} else {{ {b} }})"),
        _ => format!("({a} * {})", rng.below(1_000_000_000)),
    }
}

/// One program: definitions to feed first, the expression to run, and its
/// wall limit in seconds.
fn program(rng: &mut Rng, n: u64) -> (Vec<String>, String, u64) {
    match rng.below(8) {
        // Plain expression trees.
        0 | 1 => (Vec::new(), expr(rng, 3, None), 5),
        // Deep recursion that is not a tail call, so the stack grows.
        2 => {
            let deep = 10_000 + rng.below(2_000_000);
            (
                vec![format!(
                    "fn deep{n}(k: Int) -> Int {{ if k <= 0 {{ 0 }} else {{ 1 + deep{n}(k - 1) }} }}"
                )],
                format!("deep{n}({deep})"),
                5,
            )
        }
        // A spin that never ends: the wall limit must stop it.
        3 => (
            vec![format!("fn spin{n}(k: Int) -> Int {{ spin{n}(k + 1) }}")],
            format!("spin{n}(0)"),
            1,
        ),
        // A large list, built value by value.
        4 => {
            let len = 1_000 + rng.below(200_000);
            (
                vec![format!(
                    "fn grow{n}(k: Int, acc: List[Int]) -> List[Int] {{ if k == 0 {{ acc }} \
                     else {{ grow{n}(k - 1, acc.append(k)) }} }}"
                )],
                format!("grow{n}({len}, []).count()"),
                10,
            )
        }
        // A large string, doubled: up to 32 MiB.
        5 => {
            let doublings = 10 + rng.below(14);
            (
                vec![format!(
                    "fn dup{n}(k: Int, s: Str) -> Str {{ if k == 0 {{ s }} else {{ dup{n}(k - 1, \
                     \"{{s}}{{s}}\") }} }}"
                )],
                format!("dup{n}({doublings}, \"xy\").byteCount()"),
                10,
            )
        }
        // A loop over a large range, with the expression inside.
        6 => {
            let laps = 1_000 + rng.below(3_000_000);
            let body = expr(rng, 2, Some("i"));
            (
                Vec::new(),
                format!("for i in 1..{laps} {{ let x = {body} }}"),
                5,
            )
        }
        // Overflow bait on the way to Int's edge.
        _ => (
            Vec::new(),
            format!(
                "(9_000_000_000_000_000_000 + {} * {})",
                rng.below(4) as i64 - 1,
                expr(rng, 2, None)
            ),
            5,
        ),
    }
}

/// The outcomes a run may end in; anything else is a bug.
const OUTCOMES: [&str; 5] = ["value", "defined", "trap", "timeout", "refused"];

#[test]
fn random_programs_always_come_back() {
    let runs: u64 = std::env::var("CRAG_FUZZ")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(24);
    let seed: u64 = std::env::var("CRAG_FUZZ_SEED")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(0x00C1_7A9E);
    // Worst case, every program spends its wall limit.
    common::watchdog(120 + runs * 15, "the eval fuzz run hung");
    let mut rng = Rng(seed | 1);
    let dir = common::project("mcp-fuzz", &[]);
    let mut client = Client::start(&dir, &[]);
    for n in 0..runs {
        let (definitions, run, wall) = program(&mut rng, n);
        let at = format!(
            "seed {seed}, program {n}: {}; {run}",
            definitions.join("; ")
        );
        for definition in &definitions {
            let (failed, answer) = client.call("eval", json!({"code": definition}));
            assert!(!failed, "{at}\nthe definition failed: {answer}");
        }
        let (_, answer) = client.call("eval", json!({"code": run, "timeoutSeconds": wall}));
        // The outcome is structured, whatever happened...
        let outcome = answer["outcome"].as_str();
        assert!(
            outcome.is_some_and(|o| OUTCOMES.contains(&o))
                || answer["diagnostics"].is_array()
                || answer["error"].is_string(),
            "{at}\nno structured outcome: {answer}"
        );
        // ...and the session still answers.
        let (failed, answer) = client.call("eval", json!({"code": format!("{n} + 2")}));
        assert!(!failed, "{at}\nthe session is gone: {answer}");
        assert_eq!(
            answer["value"],
            Value::String(format!("{}", n + 2)),
            "{at}\nthe session answers wrongly: {answer}"
        );
    }
    client.finish();
}
