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

//! `crag mcp`: the agent server driven over pipes as an agent's client
//! would, with the real binary. Every wait has a bound, and a watchdog ends
//! the process if a test hangs.

mod common;

use std::io::{BufRead, BufReader, Write};
use std::path::Path;
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver};
use std::time::Duration;

use serde_json::{Value, json};

const WAIT: Duration = Duration::from_secs(30);

struct Client {
    child: Child,
    input: Option<ChildStdin>,
    messages: Receiver<Value>,
    id: i64,
}

impl Client {
    fn start(dir: &Path, args: &[&str]) -> Client {
        common::watchdog(240, "the agent server tests hung");
        let mut child = Command::new(env!("CARGO_BIN_EXE_crag"))
            .arg("mcp")
            .args(args)
            .current_dir(dir)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .unwrap();
        let input = child.stdin.take().unwrap();
        let output = child.stdout.take().unwrap();
        let (tx, messages) = mpsc::channel();
        std::thread::spawn(move || {
            for line in BufReader::new(output).lines() {
                let Ok(line) = line else { return };
                if tx.send(serde_json::from_str(&line).unwrap()).is_err() {
                    return;
                }
            }
        });
        let mut client = Client {
            child,
            input: Some(input),
            messages,
            id: 0,
        };
        let init = client.request(
            "initialize",
            json!({
                "protocolVersion": "2025-06-18",
                "capabilities": {},
                "clientInfo": {"name": "test", "version": "0"},
            }),
        );
        assert_eq!(init["result"]["serverInfo"]["name"], "crag");
        client.send(json!({"jsonrpc": "2.0", "method": "notifications/initialized"}));
        client
    }

    fn send(&mut self, message: Value) {
        let input = self.input.as_mut().unwrap();
        writeln!(input, "{message}").unwrap();
        input.flush().unwrap();
    }

    fn request(&mut self, method: &str, params: Value) -> Value {
        self.id += 1;
        let id = self.id;
        self.send(json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params}));
        loop {
            let message = self
                .messages
                .recv_timeout(WAIT)
                .unwrap_or_else(|_| panic!("no answer to {method}"));
            if message["id"] == id {
                return message;
            }
        }
    }

    /// Calls a tool: whether it failed, and its answer.
    fn call(&mut self, tool: &str, args: Value) -> (bool, Value) {
        let answer = self.request("tools/call", json!({"name": tool, "arguments": args}));
        let result = &answer["result"];
        assert!(result.is_object(), "{tool} was refused: {answer}");
        (
            result["isError"] == true,
            result["structuredContent"].clone(),
        )
    }

    /// Closes the input and waits for the server to end.
    fn finish(mut self) {
        self.input = None;
        for _ in 0..200 {
            if let Some(status) = self.child.try_wait().unwrap() {
                assert!(status.success(), "crag mcp ended with {status}");
                return;
            }
            std::thread::sleep(Duration::from_millis(50));
        }
        let _ = self.child.kill();
        panic!("crag mcp did not end when its input closed");
    }
}

impl Drop for Client {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

#[test]
fn lists_the_tools() {
    let dir = common::project("mcp-tools", &[]);
    let mut client = Client::start(&dir, &[]);
    let tools = client.request("tools/list", json!({}));
    let names: Vec<&str> = tools["result"]["tools"]
        .as_array()
        .unwrap()
        .iter()
        .map(|t| t["name"].as_str().unwrap())
        .collect();
    assert_eq!(
        names,
        ["check", "typeOf", "members", "searchStd", "eval", "test"]
    );
    client.finish();
}

#[test]
fn checks_and_types_snippets() {
    let dir = common::project("mcp-check", &[]);
    let mut client = Client::start(&dir, &[]);
    let (failed, answer) = client.call(
        "check",
        json!({"code": "fn double(x: Int) -> Int { x * \"a\" }"}),
    );
    assert!(!failed);
    assert_eq!(answer["ok"], false);
    let diagnostic = &answer["diagnostics"][0];
    assert_eq!(
        diagnostic["message"],
        "no function `multiply` takes (Int, Str)"
    );
    assert_eq!(
        (&diagnostic["line"], &diagnostic["column"]),
        (&json!(1), &json!(28))
    );

    let (_, answer) = client.call(
        "check",
        json!({"code": "fn double(x: Int) -> Int { x * 2 }"}),
    );
    assert_eq!(answer["ok"], true);

    let (failed, answer) = client.call("typeOf", json!({"expr": "[1, 2].count()"}));
    assert!(!failed, "{answer}");
    assert_eq!(answer, json!({"type": "Int", "effects": []}));

    let (failed, answer) = client.call("typeOf", json!({"expr": "nothing(1)"}));
    assert!(failed);
    assert_eq!(
        answer["diagnostics"][0]["message"],
        "`nothing` is not defined"
    );
    client.finish();
}

#[test]
fn finds_functions() {
    let dir = common::project("mcp-find", &[]);
    let mut client = Client::start(&dir, &[]);
    let (_, answer) = client.call("members", json!({"type": "Str"}));
    let functions = answer["functions"].as_array().unwrap();
    assert!(
        functions
            .iter()
            .any(|f| f["name"] == "split" && f["module"] == "std.core"),
        "{answer}"
    );

    let (_, answer) = client.call("searchStd", json!({"name": "split"}));
    let split = &answer["functions"][0];
    assert_eq!(
        split["signature"],
        "pub fn split(s: Str, separator: Str) -> List[Str]"
    );
    assert!(split["doc"].as_str().unwrap().contains("separators"));

    let (_, answer) = client.call(
        "searchStd",
        json!({"signature": "(s: Str, separator: Str)"}),
    );
    assert!(
        answer["functions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|f| f["name"] == "split")
    );
    client.finish();
}

#[test]
fn evaluates_in_the_scratch_image() {
    let dir = common::project("mcp-eval", &[]);
    let mut client = Client::start(&dir, &[]);
    let (_, answer) = client.call(
        "eval",
        json!({"code": "fn double(x: Int) -> Int { x * 2 }"}),
    );
    assert_eq!(answer["outcome"], "defined");
    let (failed, answer) = client.call("eval", json!({"code": "double(21)"}));
    assert!(!failed);
    assert_eq!(
        (&answer["value"], &answer["type"]),
        (&json!("42"), &json!("Int"))
    );

    let (failed, answer) = client.call("eval", json!({"code": "1 / 0"}));
    assert!(failed);
    assert_eq!(answer["outcome"], "trap");
    assert!(
        answer["report"]
            .as_str()
            .unwrap()
            .contains("division by zero")
    );

    // A run that never ends is stopped, and the next one runs.
    client.call(
        "eval",
        json!({"code": "fn spin(n: Int) -> Int { spin(n + 1) }"}),
    );
    let (failed, answer) = client.call("eval", json!({"code": "spin(0)", "timeoutSeconds": 1}));
    assert!(failed);
    assert_eq!(answer["outcome"], "timeout");
    let (_, answer) = client.call("eval", json!({"code": "1 + 1"}));
    assert_eq!(answer["value"], "2");

    // Code with the io effect needs the user's grant.
    client.call("eval", json!({"code": "import std.io"}));
    let (failed, answer) = client.call("eval", json!({"code": "printLine(\"hi\")"}));
    assert!(failed);
    assert_eq!(
        (&answer["outcome"], &answer["effect"]),
        (&json!("refused"), &json!("io"))
    );
    client.finish();

    let mut client = Client::start(&dir, &["--allow-io"]);
    client.call("eval", json!({"code": "import std.io"}));
    let (failed, answer) = client.call("eval", json!({"code": "printLine(\"hi\")"}));
    assert!(!failed, "{answer}");
    assert_eq!(answer["printed"], "hi\n");
    client.finish();
}

const MAIN: &str = "pub fn greeting(name: Str) -> Str { \"Hello, {name}!\" }\n";

const MAIN_TEST: &str = "import std.test

import demo.main

test \"greets\" { assertEqual(greeting(\"you\"), \"Hello, you!\") }

test \"fails\" { assertEqual(greeting(\"you\"), \"Hi\") }
";

#[test]
fn works_in_a_project_and_follows_its_files() {
    let dir = common::project(
        "mcp-project",
        &[
            ("package.crag", "package demo 0.1\nruntime 0.0\n"),
            ("main.crag", MAIN),
            ("test/main_test.crag", MAIN_TEST),
        ],
    );
    let mut client = Client::start(&dir, &[]);
    let (_, answer) = client.call("check", json!({}));
    assert_eq!(answer["ok"], true, "{answer}");

    client.call("eval", json!({"code": "import demo.main"}));
    let (_, answer) = client.call("eval", json!({"code": "greeting(\"agent\")"}));
    assert_eq!(answer["value"], "\"Hello, agent!\"");

    let (failed, answer) = client.call("test", json!({}));
    assert!(!failed, "{answer}");
    assert_eq!(answer["ok"], false);
    assert_eq!(answer["passed"], json!(["test/main_test.crag \"greets\""]));
    assert_eq!(answer["failed"][0]["name"], "test/main_test.crag \"fails\"");
    assert!(
        answer["failed"][0]["report"]
            .as_str()
            .unwrap()
            .contains("assertion failed")
    );

    let (_, answer) = client.call("test", json!({"filter": "greets"}));
    assert_eq!(answer["ok"], true, "{answer}");

    // An edit on disk is seen by the next call, and so is a new file.
    std::fs::write(
        dir.join("main.crag"),
        "pub fn greeting(name: Str) -> Str { 1 }\n",
    )
    .unwrap();
    let (_, answer) = client.call("check", json!({"file": "main.crag"}));
    assert_eq!(answer["ok"], false, "{answer}");
    assert_eq!(answer["diagnostics"][0]["file"], "main.crag");
    std::fs::write(dir.join("main.crag"), MAIN).unwrap();
    std::fs::write(dir.join("extra.crag"), "pub fn extra() -> Int { \"no\" }\n").unwrap();
    let (_, answer) = client.call("check", json!({}));
    assert_eq!(answer["diagnostics"][0]["file"], "extra.crag", "{answer}");
    client.finish();
}
