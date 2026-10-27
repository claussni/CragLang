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

//! `crag dap`: the debug adapter driven over pipes as an editor would, with
//! the real binary. Every wait has a bound, and a watchdog ends the process
//! if a test hangs.

use std::collections::VecDeque;
use std::fs;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::Once;
use std::sync::mpsc::{self, Receiver};
use std::time::{Duration, Instant};

use serde_json::{Value, json};

fn watchdog() {
    static START: Once = Once::new();
    START.call_once(|| {
        std::thread::spawn(|| {
            std::thread::sleep(Duration::from_secs(90));
            eprintln!("the debug adapter tests hung");
            std::process::abort();
        });
    });
}

const SERVER: &str = r#"import std.io

fn reply(c: Connection, n: Int) -> () {
  case c.read() {
    bytes: Bytes -> {
      let doubled = n * 2
      let written = c.write(b"done")
    }
    _ -> ()
  }
}

fn serve(l: Listener, n: Int) -> () {
  case l.accept() {
    c: Connection -> {
      reply(c, n)
      serve(l, n + 1)
    }
    _ -> ()
  }
}

fn main() -> () {
  case listen(PORT) {
    l: Listener -> serve(l, 1)
    _ -> ()
  }
}
"#;

const WAIT: Duration = Duration::from_secs(20);

struct Client {
    child: Child,
    input: Option<ChildStdin>,
    messages: Receiver<Value>,
    /// Events that arrived while waiting for something else.
    queue: VecDeque<Value>,
    seq: i64,
}

impl Client {
    fn start() -> Client {
        watchdog();
        let mut child = Command::new(env!("CARGO_BIN_EXE_crag"))
            .arg("dap")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .unwrap();
        let input = child.stdin.take().unwrap();
        let output = child.stdout.take().unwrap();
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
            child,
            input: Some(input),
            messages,
            queue: VecDeque::new(),
            seq: 1,
        }
    }

    /// Sends a request and returns its response's body; panics unless it
    /// succeeded.
    fn request(&mut self, command: &str, arguments: Value) -> Value {
        let response = self.call(command, arguments);
        assert_eq!(response["success"], true, "{command}: {response}");
        response["body"].clone()
    }

    fn call(&mut self, command: &str, arguments: Value) -> Value {
        let seq = self.seq;
        self.seq += 1;
        let message =
            json!({"seq": seq, "type": "request", "command": command, "arguments": arguments});
        let body = serde_json::to_vec(&message).unwrap();
        let input = self.input.as_mut().expect("the input is open");
        write!(input, "Content-Length: {}\r\n\r\n", body.len()).unwrap();
        input.write_all(&body).unwrap();
        input.flush().unwrap();
        let deadline = Instant::now() + WAIT;
        loop {
            let left = deadline.saturating_duration_since(Instant::now());
            let message = self
                .messages
                .recv_timeout(left)
                .expect("no response in time");
            if message["type"] == "response" && message["request_seq"] == seq {
                return message;
            }
            self.queue.push_back(message);
        }
    }

    /// The next event called `name`.
    fn event(&mut self, name: &str) -> Value {
        let deadline = Instant::now() + WAIT;
        loop {
            let message = match self.queue.pop_front() {
                Some(message) => message,
                None => {
                    let left = deadline.saturating_duration_since(Instant::now());
                    self.messages
                        .recv_timeout(left)
                        .unwrap_or_else(|_| panic!("no {name} event in time"))
                }
            };
            if message["type"] == "event" && message["event"] == name {
                return message["body"].clone();
            }
        }
    }

    /// Waits for the adapter's process to end; its status.
    fn wait(mut self) -> i32 {
        let deadline = Instant::now() + WAIT;
        loop {
            if let Some(status) = self.child.try_wait().unwrap() {
                return status.code().unwrap_or(-1);
            }
            if Instant::now() >= deadline {
                let _ = self.child.kill();
                panic!("the adapter did not end");
            }
            std::thread::sleep(Duration::from_millis(10));
        }
    }
}

fn ask(port: u16) -> String {
    let deadline = Instant::now() + WAIT;
    let mut stream = loop {
        match TcpStream::connect(("127.0.0.1", port)) {
            Ok(stream) => break stream,
            Err(e) => {
                assert!(Instant::now() < deadline, "the server never listened: {e}");
                std::thread::sleep(Duration::from_millis(10));
            }
        }
    };
    stream.set_read_timeout(Some(WAIT)).unwrap();
    stream.write_all(b"hello").unwrap();
    let mut answer = String::new();
    stream.read_to_string(&mut answer).unwrap();
    answer
}

#[test]
fn an_editor_debugs_the_app_through_the_adapter() {
    let root = std::env::temp_dir().join(format!("crag-dap-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("package.crag"),
        "package demo 0.1\nruntime 0.0\nmain demo.app\n",
    )
    .unwrap();
    let port = TcpListener::bind("127.0.0.1:0")
        .unwrap()
        .local_addr()
        .unwrap()
        .port();
    fs::write(
        root.join("app.crag"),
        SERVER.replace("PORT", &port.to_string()),
    )
    .unwrap();
    let app = root.join("app.crag");
    let line = SERVER
        .lines()
        .position(|l| l.contains("let doubled"))
        .unwrap() as u64
        + 1;

    let mut client = Client::start();
    let capabilities = client.request("initialize", json!({"adapterID": "crag"}));
    assert_eq!(capabilities["supportsConfigurationDoneRequest"], true);
    client.event("initialized");
    // Breakpoints before the launch, as editors set them.
    let set = client.request(
        "setBreakpoints",
        json!({"source": {"path": app.display().to_string()}, "breakpoints": [{"line": line}]}),
    );
    assert_eq!(set["breakpoints"][0]["line"], line);
    client.request("launch", json!({"project": root.display().to_string()}));
    client.request("configurationDone", json!({}));
    let set = client.request(
        "setBreakpoints",
        json!({"source": {"path": app.display().to_string()}, "breakpoints": [{"line": line}]}),
    );
    assert_eq!(set["breakpoints"][0]["verified"], true);

    let asker = std::thread::spawn(move || ask(port));
    let stopped = client.event("stopped");
    assert_eq!(stopped["reason"], "breakpoint");
    let thread = stopped["threadId"].as_i64().unwrap();
    let threads = client.request("threads", json!({}));
    assert!(
        threads["threads"]
            .as_array()
            .unwrap()
            .iter()
            .any(|t| t["id"] == thread)
    );
    let trace = client.request("stackTrace", json!({"threadId": thread}));
    let top = &trace["stackFrames"][0];
    assert_eq!(top["name"], "reply");
    assert_eq!(top["line"], line);
    assert_eq!(trace["stackFrames"][1]["name"], "serve");
    let scopes = client.request("scopes", json!({"frameId": top["id"]}));
    let reference = scopes["scopes"][0]["variablesReference"].clone();
    let variables = client.request("variables", json!({"variablesReference": reference}));
    let n = variables["variables"]
        .as_array()
        .unwrap()
        .iter()
        .find(|v| v["name"] == "n")
        .cloned()
        .unwrap();
    assert_eq!(n["value"], "1");

    client.request("next", json!({"threadId": thread}));
    let stopped = client.event("stopped");
    assert_eq!(stopped["reason"], "step");
    let trace = client.request("stackTrace", json!({"threadId": stopped["threadId"]}));
    assert_eq!(trace["stackFrames"][0]["line"], line + 1);

    // Without breakpoints, on to the end of the request.
    client.request(
        "setBreakpoints",
        json!({"source": {"path": app.display().to_string()}, "breakpoints": []}),
    );
    client.request("continue", json!({"threadId": stopped["threadId"]}));
    assert_eq!(asker.join().unwrap(), "done");

    client.request("disconnect", json!({}));
    assert_eq!(client.wait(), 0);
    // The app stopped with the adapter.
    assert!(TcpStream::connect(("127.0.0.1", port)).is_err());
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn the_adapter_ends_with_its_input() {
    let mut client = Client::start();
    client.request("initialize", json!({}));
    let unknown = client.call("pause", json!({"threadId": 1}));
    assert_eq!(unknown["success"], false);
    client.input = None;
    assert_eq!(client.wait(), 0);
}
