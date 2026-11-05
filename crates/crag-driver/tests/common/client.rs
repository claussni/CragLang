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

//! The agent server driven over pipes as an agent's client would, with
//! the real binary: what the MCP and fuzz tests share. Every wait has a
//! bound.

use std::io::{BufRead, BufReader, Write};
use std::path::Path;
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver};
use std::time::Duration;

use serde_json::{Value, json};

const WAIT: Duration = Duration::from_secs(30);

pub struct Client {
    child: Child,
    input: Option<ChildStdin>,
    messages: Receiver<Value>,
    id: i64,
    /// How to answer an elicitation, for a client that declared the
    /// capability, and the questions asked so far.
    pub elicit_answer: Option<Value>,
    pub asked: Vec<Value>,
}

impl Client {
    pub fn start(dir: &Path, args: &[&str]) -> Client {
        Client::start_with(dir, args, &[], None)
    }

    /// A client that answers every elicitation with `elicit_answer`, and
    /// extra environment for the server.
    pub fn start_with(
        dir: &Path,
        args: &[&str],
        envs: &[(&str, &str)],
        elicit_answer: Option<Value>,
    ) -> Client {
        super::watchdog(240, "the agent server tests hung");
        let mut child = Command::new(env!("CARGO_BIN_EXE_crag"))
            .arg("mcp")
            .args(args)
            .envs(envs.iter().map(|(k, v)| (k.to_string(), v.to_string())))
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
        let capabilities = match elicit_answer {
            Some(_) => json!({"elicitation": {}}),
            None => json!({}),
        };
        let mut client = Client {
            child,
            input: Some(input),
            messages,
            id: 0,
            elicit_answer,
            asked: Vec::new(),
        };
        let init = client.request(
            "initialize",
            json!({
                "protocolVersion": "2025-06-18",
                "capabilities": capabilities,
                "clientInfo": {"name": "test", "version": "0"},
            }),
        );
        assert_eq!(init["result"]["serverInfo"]["name"], "crag");
        client.send(json!({"jsonrpc": "2.0", "method": "notifications/initialized"}));
        client
    }

    pub fn send(&mut self, message: Value) {
        let input = self.input.as_mut().unwrap();
        writeln!(input, "{message}").unwrap();
        input.flush().unwrap();
    }

    pub fn request(&mut self, method: &str, params: Value) -> Value {
        self.id += 1;
        let id = self.id;
        self.send(json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params}));
        loop {
            let message = self
                .messages
                .recv_timeout(WAIT)
                .unwrap_or_else(|_| panic!("no answer to {method}"));
            // The server may ask the user before it answers.
            if message["method"] == "elicitation/create" {
                self.asked.push(message["params"].clone());
                let answer = self
                    .elicit_answer
                    .clone()
                    .unwrap_or_else(|| json!({"action": "decline"}));
                self.send(json!({
                    "jsonrpc": "2.0",
                    "id": message["id"],
                    "result": answer,
                }));
                continue;
            }
            if message["id"] == id {
                return message;
            }
        }
    }

    /// Calls a tool: whether it failed, and its answer.
    pub fn call(&mut self, tool: &str, args: Value) -> (bool, Value) {
        let answer = self.request("tools/call", json!({"name": tool, "arguments": args}));
        let result = &answer["result"];
        assert!(result.is_object(), "{tool} was refused: {answer}");
        (
            result["isError"] == true,
            result["structuredContent"].clone(),
        )
    }

    /// Closes the input and waits for the server to end.
    pub fn finish(mut self) {
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
