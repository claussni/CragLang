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

//! `crag lsp`: the language server driven over pipes as an editor would.
//! Every wait has a bound, and a watchdog ends the process if a test hangs.

use std::collections::VecDeque;
use std::fs;
use std::io::{BufRead, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::Once;
use std::sync::mpsc::{self, Receiver};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

use serde_json::{Value, json};

fn watchdog() {
    static START: Once = Once::new();
    START.call_once(|| {
        std::thread::spawn(|| {
            std::thread::sleep(Duration::from_secs(60));
            eprintln!("the language server tests hung");
            std::process::abort();
        });
    });
}

const MANIFEST: &str = "package demo 0.1\nruntime 0.0\nmain demo.app\n";

const SHAPE: &str = "pub type Point(x: Int, y: Int)

// The area of the rectangle from the origin to `p`.
pub fn area(p: Point) -> Int { p.x * p.y }
";

const APP: &str = "import demo.geo.shape

fn main() -> Int {
  let p = Point(x: 2, y: 3)
  area(p) + area(p)
}
";

fn project(name: &str) -> PathBuf {
    let root = std::env::temp_dir().join(format!("crag-lsp-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("geo")).unwrap();
    fs::write(root.join("package.crag"), MANIFEST).unwrap();
    fs::write(root.join("geo/shape.crag"), SHAPE).unwrap();
    fs::write(root.join("app.crag"), APP).unwrap();
    root
}

fn uri(path: &Path) -> String {
    format!("file://{}", path.display())
}

struct Client {
    input: std::io::PipeWriter,
    messages: Receiver<Value>,
    /// Notifications that arrived while waiting for a response.
    queue: VecDeque<Value>,
    next: i64,
    server: Option<JoinHandle<u8>>,
}

const WAIT: Duration = Duration::from_secs(20);

impl Client {
    fn start() -> Client {
        watchdog();
        let (server_in, input) = std::io::pipe().unwrap();
        let (output, server_out) = std::io::pipe().unwrap();
        let server = std::thread::spawn(move || crag_driver::lsp::serve(server_in, server_out));
        let (tx, messages) = mpsc::channel();
        std::thread::spawn(move || {
            let mut output = BufReader::new(output);
            loop {
                let mut length = 0;
                loop {
                    let mut line = String::new();
                    if output.read_line(&mut line).unwrap_or(0) == 0 {
                        return;
                    }
                    let line = line.trim_end();
                    if line.is_empty() {
                        break;
                    }
                    if let Some(n) = line.strip_prefix("Content-Length: ") {
                        length = n.parse().unwrap();
                    }
                }
                let mut body = vec![0; length];
                if output.read_exact(&mut body).is_err() {
                    return;
                }
                if tx.send(serde_json::from_slice(&body).unwrap()).is_err() {
                    return;
                }
            }
        });
        Client {
            input,
            messages,
            queue: VecDeque::new(),
            next: 1,
            server: Some(server),
        }
    }

    fn send(&mut self, message: Value) {
        let body = serde_json::to_vec(&message).unwrap();
        write!(self.input, "Content-Length: {}\r\n\r\n", body.len()).unwrap();
        self.input.write_all(&body).unwrap();
        self.input.flush().unwrap();
    }

    fn notify(&mut self, method: &str, params: Value) {
        self.send(json!({"jsonrpc": "2.0", "method": method, "params": params}));
    }

    /// The whole response to a request.
    fn call(&mut self, method: &str, params: Value) -> Value {
        let id = self.next;
        self.next += 1;
        self.send(json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params}));
        let deadline = Instant::now() + WAIT;
        loop {
            let left = deadline.saturating_duration_since(Instant::now());
            let message = self
                .messages
                .recv_timeout(left)
                .expect("no response in time");
            if message["id"] == id {
                return message;
            }
            self.queue.push_back(message);
        }
    }

    fn request(&mut self, method: &str, params: Value) -> Value {
        let response = self.call(method, params);
        assert!(response.get("error").is_none(), "{method}: {response}");
        response["result"].clone()
    }

    /// The next diagnostics published for `uri` that satisfy `wanted`.
    fn diagnostics(&mut self, uri: &str, wanted: impl Fn(&[Value]) -> bool) -> Vec<Value> {
        let deadline = Instant::now() + WAIT;
        loop {
            let message = match self.queue.pop_front() {
                Some(message) => message,
                None => {
                    let left = deadline.saturating_duration_since(Instant::now());
                    self.messages
                        .recv_timeout(left)
                        .expect("no diagnostics in time")
                }
            };
            if message["method"] == "textDocument/publishDiagnostics"
                && message["params"]["uri"] == uri
            {
                let list = message["params"]["diagnostics"].as_array().unwrap().clone();
                if wanted(&list) {
                    return list;
                }
            }
        }
    }

    fn initialize(&mut self, root: &Path) -> Value {
        let result = self.request(
            "initialize",
            json!({"rootUri": uri(root), "capabilities": {"general": {"positionEncodings": ["utf-16"]}}}),
        );
        self.notify("initialized", json!({}));
        result
    }

    fn open(&mut self, path: &Path) {
        let text = fs::read_to_string(path).unwrap();
        self.notify(
            "textDocument/didOpen",
            json!({"textDocument": {"uri": uri(path), "languageId": "crag", "version": 1, "text": text}}),
        );
    }

    /// Ends the session properly; the server's exit status.
    fn stop(mut self) -> u8 {
        self.request("shutdown", Value::Null);
        self.notify("exit", Value::Null);
        self.server.take().unwrap().join().unwrap()
    }
}

fn at(path: &Path, line: u32, character: u32) -> Value {
    json!({"textDocument": {"uri": uri(path)}, "position": {"line": line, "character": character}})
}

#[test]
fn diagnostics_follow_the_edits() {
    let root = project("diagnostics");
    let mut client = Client::start();
    let caps = client.initialize(&root);
    assert_eq!(caps["capabilities"]["positionEncoding"], "utf-16");
    let app = root.join("app.crag");
    client.open(&app);
    client.diagnostics(&uri(&app), |d| d.is_empty());
    // `p` becomes `q`, which is not declared.
    client.notify(
        "textDocument/didChange",
        json!({
            "textDocument": {"uri": uri(&app), "version": 2},
            "contentChanges": [{"range": {"start": {"line": 4, "character": 7}, "end": {"line": 4, "character": 8}}, "text": "q"}],
        }),
    );
    let errors = client.diagnostics(&uri(&app), |d| !d.is_empty());
    assert!(
        errors[0]["message"].as_str().unwrap().contains('q'),
        "{errors:?}"
    );
    assert_eq!(
        errors[0]["range"]["start"],
        json!({"line": 4, "character": 7})
    );
    client.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri(&app), "version": 3}, "contentChanges": [{"text": APP}]}),
    );
    client.diagnostics(&uri(&app), |d| d.is_empty());
    assert_eq!(client.stop(), 0);
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn hover_definition_and_references() {
    let root = project("navigation");
    let mut client = Client::start();
    client.initialize(&root);
    let (app, shape) = (root.join("app.crag"), root.join("geo/shape.crag"));
    client.open(&app);
    // `p` in `area(p)`: a local of type Point.
    let hover = client.request("textDocument/hover", at(&app, 4, 7));
    assert_eq!(hover["contents"]["value"], "```crag\np: Point\n```");
    // `area`: its signature and documentation.
    let hover = client.request("textDocument/hover", at(&app, 4, 3));
    let value = hover["contents"]["value"].as_str().unwrap();
    assert!(value.contains("pub fn area(p: Point) -> Int"), "{value}");
    assert!(value.contains("The area of the rectangle"), "{value}");
    // Its definition is in the other module.
    let definition = client.request("textDocument/definition", at(&app, 4, 3));
    assert_eq!(definition["uri"], uri(&shape));
    assert_eq!(
        definition["range"]["start"],
        json!({"line": 3, "character": 7})
    );
    // The definition of a local is its binding.
    let definition = client.request("textDocument/definition", at(&app, 4, 7));
    assert_eq!(
        definition["range"]["start"],
        json!({"line": 3, "character": 6})
    );
    // References: the declaration and both calls.
    let references = client.request(
        "textDocument/references",
        json!({"textDocument": {"uri": uri(&app)}, "position": {"line": 4, "character": 3}, "context": {"includeDeclaration": true}}),
    );
    let mut found: Vec<(String, Value)> = references
        .as_array()
        .unwrap()
        .iter()
        .map(|r| {
            (
                r["uri"].as_str().unwrap().to_string(),
                r["range"]["start"].clone(),
            )
        })
        .collect();
    found.sort_by_key(|(u, p)| (u.clone(), p.to_string()));
    assert_eq!(
        found,
        vec![
            (uri(&app), json!({"line": 4, "character": 12})),
            (uri(&app), json!({"line": 4, "character": 2})),
            (uri(&shape), json!({"line": 3, "character": 7})),
        ]
    );
    // A type: its declaration.
    let definition = client.request("textDocument/definition", at(&app, 3, 11));
    assert_eq!(definition["uri"], uri(&shape));
    assert_eq!(
        definition["range"]["start"],
        json!({"line": 0, "character": 9})
    );
    assert_eq!(client.stop(), 0);
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn rename_changes_every_use() {
    let root = project("rename");
    let mut client = Client::start();
    client.initialize(&root);
    let (app, shape) = (root.join("app.crag"), root.join("geo/shape.crag"));
    client.open(&app);
    let range = client.request("textDocument/prepareRename", at(&app, 4, 3));
    assert_eq!(range["start"], json!({"line": 4, "character": 2}));
    let mut params = at(&app, 4, 3);
    params["newName"] = json!("surface");
    let edit = client.request("textDocument/rename", params);
    let changes = &edit["changes"];
    assert_eq!(changes[uri(&app)].as_array().unwrap().len(), 2);
    assert_eq!(changes[uri(&shape)].as_array().unwrap().len(), 1);
    // A local, within its function.
    let mut params = at(&app, 3, 6);
    params["newName"] = json!("corner");
    let edit = client.request("textDocument/rename", params);
    assert_eq!(edit["changes"][uri(&app)].as_array().unwrap().len(), 3);
    // Neither a keyword nor a name of std.
    let mut params = at(&app, 3, 6);
    params["newName"] = json!("case");
    assert!(
        client
            .call("textDocument/rename", params)
            .get("error")
            .is_some()
    );
    let response = client.call("textDocument/prepareRename", at(&app, 3, 10));
    assert!(response.get("error").is_none());
    assert_eq!(client.stop(), 0);
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn completion_formatting_and_symbols() {
    let root = project("completion");
    let mut client = Client::start();
    client.initialize(&root);
    let app = root.join("app.crag");
    let text =
        "import demo.geo.shape\n\nfn main() -> Int {\n  let p = Point(x: 2, y: 3)\n  p.\n}\n";
    fs::write(&app, text).unwrap();
    client.open(&app);
    let items = client.request("textDocument/completion", at(&app, 4, 4));
    let labels: Vec<&str> = items
        .as_array()
        .unwrap()
        .iter()
        .map(|i| i["label"].as_str().unwrap())
        .collect();
    for wanted in ["x", "y", "area"] {
        assert!(labels.contains(&wanted), "{wanted} missing from {labels:?}");
    }
    // Names in scope, locals among them.
    let items = client.request("textDocument/completion", at(&app, 4, 2));
    let labels: Vec<&str> = items
        .as_array()
        .unwrap()
        .iter()
        .map(|i| i["label"].as_str().unwrap())
        .collect();
    for wanted in ["p", "area", "Point", "main"] {
        assert!(labels.contains(&wanted), "{wanted} missing");
    }
    let shape = root.join("geo/shape.crag");
    fs::write(
        &shape,
        "pub type Point(x: Int,y: Int)\npub fn area(p: Point) -> Int {\n  p.x*p.y\n}\n",
    )
    .unwrap();
    client.open(&shape);
    let edits = client.request("textDocument/formatting", json!({"textDocument": {"uri": uri(&shape)}, "options": {"tabSize": 2, "insertSpaces": true}}));
    assert_eq!(
        edits[0]["newText"],
        "pub type Point(x: Int, y: Int)\npub fn area(p: Point) -> Int { p.x * p.y }\n"
    );
    let symbols = client.request(
        "textDocument/documentSymbol",
        json!({"textDocument": {"uri": uri(&shape)}}),
    );
    let names: Vec<&str> = symbols
        .as_array()
        .unwrap()
        .iter()
        .map(|s| s["name"].as_str().unwrap())
        .collect();
    assert_eq!(names, ["Point", "area"]);
    assert_eq!(client.stop(), 0);
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn the_protocol_rules_are_kept() {
    let mut client = Client::start();
    let early = client.call("textDocument/hover", json!({}));
    assert_eq!(early["error"]["code"], -32002);
    let root = project("protocol");
    client.initialize(&root);
    let unknown = client.call("crag/nothing", json!({}));
    assert_eq!(unknown["error"]["code"], -32601);
    // A request on a document that is not open.
    let closed = client.call("textDocument/hover", at(&root.join("app.crag"), 0, 0));
    assert_eq!(closed["error"]["code"], -32602);
    // Cancelling what already finished does nothing.
    client.notify("$/cancelRequest", json!({"id": 1}));
    assert_eq!(client.stop(), 0);
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn the_server_ends_with_its_input() {
    let mut client = Client::start();
    client.notify("exit", Value::Null);
    // `exit` without `shutdown` is an error exit.
    assert_eq!(client.server.take().unwrap().join().unwrap(), 1);
    let client = Client::start();
    let Client { input, server, .. } = client;
    drop(input);
    assert_eq!(server.unwrap().join().unwrap(), 1);
}

#[test]
fn every_request_is_answered_while_edits_arrive() {
    let root = project("edits");
    let mut client = Client::start();
    client.initialize(&root);
    let app = root.join("app.crag");
    client.open(&app);
    let mut ids = Vec::new();
    for round in 0..40 {
        let id = 1000 + round;
        let method = [
            "textDocument/hover",
            "textDocument/references",
            "textDocument/completion",
        ][round as usize % 3];
        let mut params = at(&app, 4, 3);
        params["context"] = json!({"includeDeclaration": true});
        client.send(json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params}));
        ids.push(id);
        let text = format!("{APP}\nfn extra{round}() -> Int {{ {round} }}\n");
        client.notify(
            "textDocument/didChange",
            json!({"textDocument": {"uri": uri(&app), "version": round + 2}, "contentChanges": [{"text": text}]}),
        );
    }
    let deadline = Instant::now() + WAIT;
    while !ids.is_empty() {
        let left = deadline.saturating_duration_since(Instant::now());
        let message = client
            .messages
            .recv_timeout(left)
            .expect("a request was never answered");
        if let Some(id) = message["id"].as_i64() {
            let fine = message.get("result").is_some() || message["error"]["code"] == -32801;
            assert!(fine, "{message}");
            ids.retain(|&i| i != id);
        }
    }
    assert_eq!(client.stop(), 0);
    let _ = fs::remove_dir_all(&root);
}
