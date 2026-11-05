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

use std::io::{Read as _, Write};
use std::net::{TcpListener, TcpStream};
use std::time::Duration;

use common::client::Client;
use serde_json::json;

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
        [
            "check",
            "typeOf",
            "members",
            "searchStd",
            "explain",
            "eval",
            "test",
            "fmt",
            "refactor",
            "reload"
        ]
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
    assert_eq!(diagnostic["code"], "E0303");
    assert_eq!(diagnostic["resource"], "crag://diagnostic/E0303");

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

    // The project resources follow the project the server started in.
    let manifest = client.request("resources/read", json!({"uri": "crag://project/manifest"}));
    let text = manifest["result"]["contents"][0]["text"].as_str().unwrap();
    assert!(text.contains("package demo 0.1"), "{text}");
    let api = client.request("resources/read", json!({"uri": "crag://project/api"}));
    let text = api["result"]["contents"][0]["text"].as_str().unwrap();
    assert!(text.contains("pub fn greeting(name: Str) -> Str"), "{text}");

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

#[test]
fn explains_diagnostics() {
    let dir = common::project("mcp-explain", &[]);
    let mut client = Client::start(&dir, &[]);
    let (failed, answer) = client.call("explain", json!({"code": "e0301"}));
    assert!(!failed, "{answer}");
    assert_eq!(answer["code"], "E0301");
    assert!(answer["failing"].as_str().unwrap().contains("fn "));
    assert!(answer["spec"].as_str().unwrap().starts_with('§'));

    let (failed, answer) = client.call("explain", json!({"code": "E9999"}));
    assert!(failed);
    assert!(answer["error"].as_str().unwrap().contains("E9999"));

    let listed = client.request("resources/list", json!({}));
    let uris: Vec<&str> = listed["result"]["resources"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| r["uri"].as_str().unwrap())
        .collect();
    assert!(uris.contains(&"crag://diagnostic/E0301"), "{listed}");
    let templates = client.request("resources/templates/list", json!({}));
    let templates: Vec<&str> = templates["result"]["resourceTemplates"]
        .as_array()
        .unwrap()
        .iter()
        .map(|t| t["uriTemplate"].as_str().unwrap())
        .collect();
    assert!(
        templates.contains(&"crag://diagnostic/{code}"),
        "{templates:?}"
    );
    assert!(
        templates.contains(&"crag://spec/{section}"),
        "{templates:?}"
    );

    let read = client.request("resources/read", json!({"uri": "crag://diagnostic/E0301"}));
    let contents = &read["result"]["contents"][0];
    assert_eq!(contents["mimeType"], "text/markdown");
    assert!(contents["text"].as_str().unwrap().starts_with("# E0301: "));
    let missing = client.request("resources/read", json!({"uri": "crag://diagnostic/E9999"}));
    assert!(missing["error"].is_object(), "{missing}");
    client.finish();
}

#[test]
fn serves_the_knowledge_resources() {
    let dir = common::project("mcp-knowledge", &[]);
    let mut client = Client::start(&dir, &[]);
    let listed = client.request("resources/list", json!({}));
    let uris: Vec<&str> = listed["result"]["resources"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| r["uri"].as_str().unwrap())
        .collect();
    for uri in [
        "crag://primer",
        "crag://principles",
        "crag://spec/8",
        "crag://spec/D",
        "crag://std/std.io",
        "crag://project/api",
        "crag://project/manifest",
    ] {
        assert!(uris.contains(&uri), "{uri} is not listed");
    }
    // Sections are listed by chapter only; deeper ones are still read.
    assert!(!uris.contains(&"crag://spec/8.2"));

    let read = |client: &mut Client, uri: &str| {
        let answer = client.request("resources/read", json!({"uri": uri}));
        answer["result"]["contents"][0]["text"]
            .as_str()
            .unwrap_or_else(|| panic!("{uri} was not read: {answer}"))
            .to_string()
    };
    let primer = read(&mut client, "crag://primer");
    assert!(primer.contains("§8.2"), "{primer}");
    let section = read(&mut client, "crag://spec/8.2");
    assert!(section.starts_with("### 8.2 "), "{section}");
    assert!(section.contains("no `?` propagation operator"));
    let chapter = read(&mut client, "crag://spec/8");
    assert!(chapter.contains("### 8.5 Prefixes"));
    let io = read(&mut client, "crag://std/std.io");
    assert!(io.contains("printLine"), "{io}");

    let missing = client.request("resources/read", json!({"uri": "crag://spec/99"}));
    assert!(missing["error"].is_object(), "{missing}");
    client.finish();
}

const UNFORMATTED: &str = "pub fn greeting(name: Str) -> Str  {  \"Hello, {name}!\" }\n";

#[test]
fn writing_tools_ask_the_user() {
    let dir = common::project(
        "mcp-write",
        &[
            ("package.crag", "package demo 0.1\nruntime 0.0\n"),
            ("main.crag", UNFORMATTED),
            ("test/main_test.crag", MAIN_TEST),
        ],
    );
    // A client that cannot be asked gets no change.
    let mut blind = Client::start(&dir, &[]);
    let (failed, answer) = blind.call("fmt", json!({}));
    assert!(failed);
    assert!(
        answer["error"].as_str().unwrap().contains("cannot ask"),
        "{answer}"
    );
    blind.finish();
    assert_eq!(
        std::fs::read_to_string(dir.join("main.crag")).unwrap(),
        UNFORMATTED
    );

    // A decline leaves the files alone.
    let mut client = Client::start_with(&dir, &[], &[], Some(json!({"action": "decline"})));
    let (failed, answer) = client.call("fmt", json!({}));
    assert!(failed);
    assert_eq!(answer["applied"], false, "{answer}");
    assert_eq!(
        std::fs::read_to_string(dir.join("main.crag")).unwrap(),
        UNFORMATTED
    );
    client.finish();

    // An accept formats, and the question names the file.
    let mut client = Client::start_with(
        &dir,
        &[],
        &[],
        Some(json!({"action": "accept", "content": {}})),
    );
    let (failed, answer) = client.call("fmt", json!({}));
    assert!(!failed, "{answer}");
    assert_eq!(answer["formatted"], json!(["main.crag"]));
    assert_eq!(
        std::fs::read_to_string(dir.join("main.crag")).unwrap(),
        MAIN
    );
    let question = client.asked.last().unwrap()["message"].as_str().unwrap();
    assert!(question.contains("main.crag"), "{question}");
    // Nothing to format the second time, so nothing is asked.
    let asked = client.asked.len();
    let (_, answer) = client.call("fmt", json!({}));
    assert_eq!(answer["formatted"], json!([]));
    assert_eq!(client.asked.len(), asked);

    // A rename changes the declaration and the uses, after the question.
    let (failed, answer) = client.call(
        "refactor",
        json!({"kind": "rename", "file": "main.crag", "line": 1, "column": 8, "to": "welcome"}),
    );
    assert!(!failed, "{answer}");
    assert_eq!(answer["renamed"], "greeting");
    assert_eq!(answer["places"], 3, "{answer}");
    let main = std::fs::read_to_string(dir.join("main.crag")).unwrap();
    assert!(main.contains("pub fn welcome"), "{main}");
    let tests = std::fs::read_to_string(dir.join("test/main_test.crag")).unwrap();
    assert!(!tests.contains("greeting("), "{tests}");
    assert_eq!(tests.matches("welcome(").count(), 2, "{tests}");
    let (_, answer) = client.call("check", json!({}));
    assert_eq!(answer["ok"], true, "{answer}");

    // A name declared in std cannot change: `Str` at column 22.
    let asked = client.asked.len();
    let (failed, answer) = client.call(
        "refactor",
        json!({"kind": "rename", "file": "main.crag", "line": 1, "column": 22, "to": "Text"}),
    );
    assert!(failed);
    assert!(
        answer["error"].as_str().unwrap().contains("cannot change"),
        "{answer}"
    );
    assert_eq!(client.asked.len(), asked, "refused before asking");
    client.finish();
}

#[test]
fn yes_to_all_covers_the_session() {
    let dir = common::project(
        "mcp-yes",
        &[
            ("package.crag", "package demo 0.1\nruntime 0.0\n"),
            ("main.crag", UNFORMATTED),
            ("extra.crag", "pub fn extra() -> Int  { 1 }\n"),
        ],
    );
    let mut client = Client::start_with(
        &dir,
        &[],
        &[],
        Some(json!({"action": "accept", "content": {"always": true}})),
    );
    let (failed, answer) = client.call("fmt", json!({"file": "main.crag"}));
    assert!(!failed, "{answer}");
    assert_eq!(client.asked.len(), 1);
    // The grant holds: the next change applies without a question.
    let (failed, answer) = client.call("fmt", json!({"file": "extra.crag"}));
    assert!(!failed, "{answer}");
    assert_eq!(answer["formatted"], json!(["extra.crag"]));
    assert_eq!(client.asked.len(), 1);
    client.finish();
}

#[test]
fn the_io_grant_comes_from_the_user() {
    let dir = common::project("mcp-io-grant", &[]);
    // Declined: refused, and the question was put.
    let mut client = Client::start_with(&dir, &[], &[], Some(json!({"action": "decline"})));
    client.call("eval", json!({"code": "import std.io"}));
    let (failed, answer) = client.call("eval", json!({"code": "printLine(\"hi\")"}));
    assert!(failed);
    assert_eq!(answer["outcome"], "refused", "{answer}");
    assert!(
        client.asked.last().unwrap()["message"]
            .as_str()
            .unwrap()
            .contains("io"),
    );
    client.finish();

    // Accepted: the grant holds for the session, with one question.
    let mut client = Client::start_with(
        &dir,
        &[],
        &[],
        Some(json!({"action": "accept", "content": {}})),
    );
    client.call("eval", json!({"code": "import std.io"}));
    let (failed, answer) = client.call("eval", json!({"code": "printLine(\"hi\")"}));
    assert!(!failed, "{answer}");
    assert_eq!(answer["printed"], "hi\n");
    let (failed, _) = client.call("eval", json!({"code": "printLine(\"again\")"}));
    assert!(!failed);
    assert_eq!(client.asked.len(), 1);
    client.finish();
}

#[test]
fn serves_the_prompts() {
    let dir = common::project("mcp-prompts", &[]);
    let mut client = Client::start(&dir, &[]);
    let listed = client.request("prompts/list", json!({}));
    let names: Vec<&str> = listed["result"]["prompts"]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| p["name"].as_str().unwrap())
        .collect();
    assert_eq!(
        names,
        [
            "crag-principles",
            "crag-write-module",
            "crag-fix-diagnostics"
        ]
    );

    let prompt = client.request(
        "prompts/get",
        json!({"name": "crag-write-module", "arguments": {"module": "demo.parser"}}),
    );
    let text = prompt["result"]["messages"][0]["content"]["text"]
        .as_str()
        .unwrap();
    assert!(text.contains("demo.parser"), "{text}");
    assert!(text.contains("crag://primer"), "{text}");

    let missing = client.request("prompts/get", json!({"name": "crag-write-module"}));
    assert!(
        missing["error"]["message"]
            .as_str()
            .unwrap()
            .contains("`module` is missing")
    );

    let prompt = client.request("prompts/get", json!({"name": "crag-fix-diagnostics"}));
    let text = prompt["result"]["messages"][0]["content"]["text"]
        .as_str()
        .unwrap();
    assert!(text.contains("the project"), "{text}");
    client.finish();
}

#[test]
fn counts_the_codes_agents_hit() {
    let dir = common::project("mcp-stats", &[]);
    let home = common::project("mcp-stats-home", &[]);
    let mut client = Client::start_with(
        &dir,
        &[],
        &[
            ("CRAG_AGENT_STATS", "1"),
            ("CRAG_HOME", home.to_str().unwrap()),
        ],
        None,
    );
    client.call(
        "check",
        json!({"code": "fn double(x: Int) -> Int { x * \"a\" }"}),
    );
    client.call(
        "check",
        json!({"code": "fn triple(x: Int) -> Int { x * \"a\" }"}),
    );
    client.finish();
    let stats = std::fs::read_to_string(home.join("agent-stats")).unwrap();
    let line = stats.lines().find(|l| l.contains("E0303")).unwrap();
    assert!(line.ends_with(" E0303 2"), "{stats}");
}

/// The reload test's app: a server that answers each connection and waits
/// for the next, as crates/crag-driver/tests/reload.rs runs it.
const APP: &str = r#"import std.io

fn answer() -> Bytes { b"v1" }

fn reply(c: Connection) -> () {
  case c.read() {
    bytes: Bytes -> {
      let written = c.write(answer())
    }
    _ -> ()
  }
}

fn serve(l: Listener) -> () {
  case l.accept() {
    c: Connection -> {
      reply(c)
      serve(l)
    }
    _ -> ()
  }
}

fn main() -> () {
  case listen(PORT) {
    l: Listener -> serve(l)
    _ -> ()
  }
}
"#;

/// What the app answers a new connection.
fn ask(port: u16) -> String {
    let deadline = std::time::Instant::now() + Duration::from_secs(20);
    let mut stream = loop {
        match TcpStream::connect(("127.0.0.1", port)) {
            Ok(stream) => break stream,
            Err(e) => {
                assert!(
                    std::time::Instant::now() < deadline,
                    "the app never listened: {e}"
                );
                std::thread::sleep(Duration::from_millis(10));
            }
        }
    };
    stream
        .set_read_timeout(Some(Duration::from_secs(20)))
        .unwrap();
    stream.write_all(b"hello").unwrap();
    let mut answer = String::new();
    stream.read_to_string(&mut answer).unwrap();
    answer
}

#[test]
fn reload_starts_the_app_and_swaps_its_code() {
    let port = TcpListener::bind("127.0.0.1:0")
        .unwrap()
        .local_addr()
        .unwrap()
        .port();
    let app = APP.replace("PORT", &port.to_string());
    let dir = common::project(
        "mcp-reload",
        &[
            (
                "package.crag",
                "package demo 0.1\nruntime 0.0\nmain demo.app\n",
            ),
            ("app.crag", &app),
        ],
    );
    let mut client = Client::start_with(
        &dir,
        &[],
        &[],
        Some(json!({"action": "accept", "content": {}})),
    );
    let (failed, answer) = client.call("reload", json!({}));
    assert!(!failed, "{answer}");
    assert_eq!(answer["started"], true);
    assert_eq!(ask(port), "v1");

    std::fs::write(dir.join("app.crag"), app.replace("v1", "v2")).unwrap();
    let (failed, answer) = client.call("reload", json!({}));
    assert!(!failed, "{answer}");
    assert_eq!(answer["started"], false);
    assert!(
        answer["report"].as_str().unwrap().contains("reloaded"),
        "{answer}"
    );
    assert_eq!(ask(port), "v2");
    client.finish();
}
