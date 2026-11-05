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

//! The agent server's tools (Implementation Plan §11.12.5–§11.12.7): what
//! each takes and answers, as JSON.

use std::io::Read;
use std::process::{Command, Stdio};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::time::{Duration, Instant};

use crag_hir::{ItemKind, item_tree};
use crag_mcp::{CallError, Outcome, ToolSpec};
use serde_json::{Map, Value, json};

use super::AgentServer;
use crate::diagnostics::{Located, check, locate_error};
use crate::lsp::analysis::{documentation, signature_text};
use crate::repl::{EvalOutput, is_definition};

/// How long `eval` may run, unless the call says otherwise, and at most.
const EVAL_WALL: u64 = 10;
const EVAL_WALL_MAX: u64 = 120;

/// How long `test` may run, unless the call says otherwise, and at most.
const TEST_WALL: u64 = 120;
const TEST_WALL_MAX: u64 = 600;

/// How long an interrupted run may take to stop before its image is
/// killed.
const GRACE: Duration = Duration::from_secs(2);

/// How many functions `searchStd` lists at most.
const SEARCH_LIMIT: usize = 50;

fn project_arg() -> Value {
    json!({
        "type": "string",
        "description": "A directory with a package.crag, relative to where the server started. \
                        Without it, that directory's project, or std alone."
    })
}

/// The tools, as the server advertises them.
pub fn specs() -> Vec<ToolSpec> {
    vec![
        ToolSpec {
            name: "check",
            title: "Check Crag code",
            description: "Type-checks Crag code and returns its diagnostics. With `code`, checks a \
                          snippet as REPL input, without keeping it: definitions, or an \
                          expression. A snippet sees std's prelude and what `eval` defined or \
                          imported before, so `import std.io` or a project module such as \
                          `import demo.main` with `eval` first, or put the import in the snippet. \
                          With `file`, checks one module file of the project; with neither, the \
                          whole project.",
            input_schema: json!({
                "type": "object",
                "properties": {
                    "code": {"type": "string", "description": "A definition or an expression."},
                    "file": {"type": "string", "description": "A module file, relative to the project's root."},
                    "project": project_arg(),
                },
            }),
            destructive: false,
        },
        ToolSpec {
            name: "typeOf",
            title: "Type of an expression",
            description: "The inferred type of a Crag expression, with its error union, and its \
                          effects (io, ref, signal), without running it.",
            input_schema: json!({
                "type": "object",
                "properties": {
                    "expr": {"type": "string", "description": "A Crag expression."},
                    "project": project_arg(),
                },
                "required": ["expr"],
            }),
            destructive: false,
        },
        ToolSpec {
            name: "members",
            title: "Members of a type",
            description: "The fields of a Crag type and the functions in scope that can be called \
                          on its values with `.` (UFCS), each with its signature and module.",
            input_schema: json!({
                "type": "object",
                "properties": {
                    "type": {"type": "string", "description": "A Crag type, such as `Str` or `[Int]`."},
                    "project": project_arg(),
                },
                "required": ["type"],
            }),
            destructive: false,
        },
        ToolSpec {
            name: "searchStd",
            title: "Search std and dependencies",
            description: "Finds public functions of std and the project's dependencies whose name \
                          contains `name`, or whose signature contains `signature` (spaces are \
                          ignored), with their signatures and documentation.",
            input_schema: json!({
                "type": "object",
                "properties": {
                    "name": {"type": "string", "description": "Part of a function's name, any case."},
                    "signature": {"type": "string", "description": "Part of a signature, such as `-> Str`."},
                    "project": project_arg(),
                },
            }),
            destructive: false,
        },
        ToolSpec {
            name: "eval",
            title: "Evaluate Crag code",
            description: "Runs Crag code in the scratch image, as REPL input: definitions and \
                          imports are added to the session and kept for later calls in the same \
                          project; an expression is run and its value shown with its type. A trap \
                          or the time limit comes back as the outcome. Code with the io effect is \
                          refused unless the user started the server with --allow-io.",
            input_schema: json!({
                "type": "object",
                "properties": {
                    "code": {"type": "string", "description": "A definition or an expression."},
                    "timeoutSeconds": {
                        "type": "integer", "minimum": 1, "maximum": EVAL_WALL_MAX,
                        "description": format!("Wall-clock limit, {EVAL_WALL} by default."),
                    },
                    "project": project_arg(),
                },
                "required": ["code"],
            }),
            destructive: false,
        },
        ToolSpec {
            name: "test",
            title: "Run tests",
            description: "Runs the project's test declarations, as `crag test` does, and returns \
                          the tests that passed and those that failed with their failed \
                          assertions and traps.",
            input_schema: json!({
                "type": "object",
                "properties": {
                    "filter": {"type": "string", "description": "Runs only tests whose label contains it."},
                    "timeoutSeconds": {
                        "type": "integer", "minimum": 1, "maximum": TEST_WALL_MAX,
                        "description": format!("Wall-clock limit, {TEST_WALL} by default."),
                    },
                    "project": project_arg(),
                },
            }),
            destructive: false,
        },
    ]
}

/// Answers a call.
pub fn call(
    server: &mut AgentServer,
    tool: &str,
    args: &Map<String, Value>,
) -> Result<Outcome, CallError> {
    let project = text_arg(args, "project")?;
    let project = project.as_deref();
    let answer = match tool {
        "check" => check_tool(
            server,
            project,
            text_arg(args, "code")?,
            text_arg(args, "file")?,
        ),
        "typeOf" => type_of(server, project, &required(args, "expr")?),
        "members" => members(server, project, &required(args, "type")?),
        "searchStd" => search_std(
            server,
            project,
            text_arg(args, "name")?,
            text_arg(args, "signature")?,
        ),
        "eval" => {
            let wall = seconds(args, EVAL_WALL, EVAL_WALL_MAX)?;
            eval(server, project, &required(args, "code")?, wall)
        }
        "test" => {
            let wall = seconds(args, TEST_WALL, TEST_WALL_MAX)?;
            test(server, project, text_arg(args, "filter")?, wall)
        }
        _ => return Err(CallError::UnknownTool(tool.into())),
    };
    Ok(match answer {
        Ok(value) => Outcome::Done(value),
        Err(Failure::Answer(value)) => Outcome::Failed(value),
        Err(Failure::Message(why)) => Outcome::Failed(json!({ "error": why })),
    })
}

/// A tool that ran and failed: with an answer of its own, or a message.
enum Failure {
    Answer(Value),
    Message(String),
}

impl From<String> for Failure {
    fn from(why: String) -> Failure {
        Failure::Message(why)
    }
}

type Answer = Result<Value, Failure>;

fn text_arg(args: &Map<String, Value>, name: &str) -> Result<Option<String>, CallError> {
    match args.get(name) {
        None | Some(Value::Null) => Ok(None),
        Some(Value::String(text)) => Ok(Some(text.clone())),
        Some(_) => Err(CallError::InvalidArguments(format!(
            "`{name}` must be a string"
        ))),
    }
}

fn required(args: &Map<String, Value>, name: &str) -> Result<String, CallError> {
    text_arg(args, name)?.ok_or_else(|| CallError::InvalidArguments(format!("`{name}` is missing")))
}

fn seconds(args: &Map<String, Value>, default: u64, max: u64) -> Result<Duration, CallError> {
    let seconds = match args.get("timeoutSeconds") {
        None | Some(Value::Null) => default,
        Some(value) => match value.as_u64() {
            Some(s) if (1..=max).contains(&s) => s,
            _ => {
                return Err(CallError::InvalidArguments(format!(
                    "`timeoutSeconds` must be a whole number from 1 to {max}"
                )));
            }
        },
    };
    Ok(Duration::from_secs(seconds))
}

fn located_json(found: &[Located]) -> Value {
    let diagnostics: Vec<Value> = found
        .iter()
        .map(|l| {
            json!({
                "file": l.file,
                "line": l.line,
                "column": l.column,
                "endLine": l.end_line,
                "endColumn": l.end_column,
                "message": l.message,
            })
        })
        .collect();
    let text: String = found.iter().map(|l| l.rendered.as_str()).collect();
    json!({ "diagnostics": diagnostics, "text": text })
}

/// The errors as a failed tool's answer.
fn errors(found: &[Located]) -> Failure {
    Failure::Answer(located_json(found))
}

fn check_tool(
    server: &mut AgentServer,
    project: Option<&str>,
    code: Option<String>,
    file: Option<String>,
) -> Answer {
    let context = server.context(project)?;
    let found = match (code, file) {
        (Some(code), _) => context.repl.check_input(&code),
        (None, file) => {
            if context.root.is_none() {
                return Err("check without `code` needs a project".to_string().into());
            }
            let project = context.repl.project();
            if let Some(file) = &file
                && !project.own().iter().any(|f| f.shown == *file)
            {
                return Err(format!("the project has no module file {file}").into());
            }
            let session = project.module(crag_hir::SESSION);
            check(project)
                .iter()
                .filter(|d| Some(d.module) != session)
                .filter(|d| {
                    file.as_ref()
                        .is_none_or(|f| project.file(d.module).shown == *f)
                })
                .map(|d| {
                    let shown = &project.file(d.module).shown;
                    locate_error(&d.message, shown, project.source(d.module), d.range.clone())
                })
                .collect()
        }
    };
    let mut answer = located_json(&found);
    answer["ok"] = json!(found.is_empty());
    Ok(answer)
}

fn type_of(server: &mut AgentServer, project: Option<&str>, expr: &str) -> Answer {
    let context = server.context(project)?;
    let (ty, effects) = context.repl.type_of(expr).map_err(|e| errors(&e))?;
    Ok(json!({ "type": ty, "effects": effects.names() }))
}

fn members(server: &mut AgentServer, project: Option<&str>, ty: &str) -> Answer {
    let context = server.context(project)?;
    let members = context.repl.members(ty).map_err(|e| errors(&e))?;
    let (fields, functions): (Vec<_>, Vec<_>) = members.into_iter().partition(|m| m.field);
    Ok(json!({
        "fields": fields
            .iter()
            .map(|m| json!({ "name": m.name, "type": m.detail }))
            .collect::<Vec<_>>(),
        "functions": functions
            .iter()
            .map(|m| json!({ "name": m.name, "signature": m.detail, "module": m.module }))
            .collect::<Vec<_>>(),
    }))
}

fn search_std(
    server: &mut AgentServer,
    project: Option<&str>,
    name: Option<String>,
    signature: Option<String>,
) -> Answer {
    if name.is_none() && signature.is_none() {
        return Err("give `name`, `signature` or both".to_string().into());
    }
    let context = server.context(project)?;
    let project = context.repl.project();
    let db = &project.db;
    let squeeze = |s: &str| s.split_whitespace().collect::<String>();
    let name = name.map(|n| n.to_lowercase());
    let signature = signature.as_deref().map(squeeze);
    let own: Vec<_> = project.own().iter().map(|f| f.module).collect();
    let mut found = Vec::new();
    let mut more = false;
    for file in project.files.iter().filter(|f| !own.contains(&f.module)) {
        for item in &item_tree(db, file.module).items {
            if !item.public || *item.id.kind(db) != ItemKind::Function {
                continue;
            }
            let item_name = item.id.name(db).text(db);
            let Some(text) = signature_text(db, item.id) else {
                continue;
            };
            let named = name
                .as_ref()
                .is_none_or(|n| item_name.to_lowercase().contains(n));
            let typed = signature
                .as_ref()
                .is_none_or(|s| squeeze(&text).contains(s.as_str()));
            if !(named && typed) {
                continue;
            }
            if found.len() == SEARCH_LIMIT {
                more = true;
                break;
            }
            found.push(json!({
                "name": item_name,
                "module": file.module.path(db),
                "signature": text,
                "doc": documentation(db, item.id),
            }));
        }
    }
    Ok(json!({ "functions": found, "more": more }))
}

/// Stops a run that takes too long: interrupts its image at the limit and
/// kills it if it does not stop soon after.
struct Watchdog {
    done: mpsc::Sender<()>,
    fired: Arc<AtomicBool>,
    thread: Option<std::thread::JoinHandle<()>>,
}

impl Watchdog {
    fn start(pid: u32, limit: Duration) -> Watchdog {
        let (done, finished) = mpsc::channel::<()>();
        let fired = Arc::new(AtomicBool::new(false));
        let flag = fired.clone();
        let thread = std::thread::spawn(move || {
            if finished.recv_timeout(limit) != Err(mpsc::RecvTimeoutError::Timeout) {
                return;
            }
            flag.store(true, Ordering::SeqCst);
            // SAFETY: signalling a process changes no state of this one.
            unsafe { libc::kill(pid as libc::pid_t, libc::SIGINT) };
            if finished.recv_timeout(GRACE) == Err(mpsc::RecvTimeoutError::Timeout) {
                // SAFETY: as above.
                unsafe { libc::kill(pid as libc::pid_t, libc::SIGKILL) };
            }
        });
        Watchdog {
            done,
            fired,
            thread: Some(thread),
        }
    }

    /// Whether the limit was reached, once the run ended.
    fn finish(mut self) -> bool {
        let _ = self.done.send(());
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
        self.fired.load(Ordering::SeqCst)
    }
}

fn eval(server: &mut AgentServer, project: Option<&str>, code: &str, wall: Duration) -> Answer {
    let io_eval = server.grants.io_eval;
    let context = server.context(project)?;
    let repl = &mut context.repl;
    let code = code.trim();
    if code.starts_with(':') {
        return Err("eval takes Crag code; REPL commands are not available"
            .to_string()
            .into());
    }
    let mut ty = None;
    if !is_definition(code) {
        let (shown, effects) = repl.type_of(code).map_err(|e| errors(&e))?;
        if effects.has_io() && !io_eval {
            return Err(Failure::Answer(json!({
                "outcome": "refused",
                "effect": "io",
                "error": "the code has the io effect, which eval runs only when the user \
                          starts the server with --allow-io",
            })));
        }
        ty = Some(shown);
    }
    // What ran before belongs to no call.
    let _ = repl.take_printed();
    let pid = repl.scratch().session().scratch().pid();
    let watchdog = Watchdog::start(pid, wall);
    let started = Instant::now();
    let result = repl.eval_input(code);
    let timed_out = watchdog.finish();
    let printed = repl.take_printed();
    let millis = started.elapsed().as_millis() as u64;
    if timed_out {
        return Err(Failure::Answer(json!({
            "outcome": "timeout",
            "error": format!("the run was stopped after {} s", wall.as_secs()),
            "printed": printed,
        })));
    }
    match result {
        Ok(EvalOutput::Nothing) => Ok(json!({ "outcome": "defined", "printed": printed })),
        Ok(EvalOutput::Value(value)) => Ok(json!({
            "outcome": "value",
            "value": value,
            "type": ty,
            "printed": printed,
            "millis": millis,
        })),
        Ok(EvalOutput::Stopped(report)) => Err(Failure::Answer(json!({
            "outcome": "trap",
            "report": report,
            "printed": printed,
        }))),
        Ok(other) => Ok(json!({ "outcome": "text", "text": other.render() })),
        Err(rendered) => Err(Failure::Answer(json!({
            "outcome": "error",
            "text": rendered,
            "printed": printed,
        }))),
    }
}

fn test(
    server: &mut AgentServer,
    project: Option<&str>,
    filter: Option<String>,
    wall: Duration,
) -> Answer {
    let Some(root) = server.root(project)? else {
        return Err("test needs a project".to_string().into());
    };
    let mut command = Command::new(&server.command.program);
    command
        .arg("test")
        .args(&filter)
        .current_dir(&root)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let (output, status) = run_bounded(command, wall)?;
    let Some(status) = status else {
        return Err(Failure::Answer(json!({
            "outcome": "timeout",
            "error": format!("the tests were stopped after {} s", wall.as_secs()),
            "output": output,
        })));
    };
    let report = parse_test_output(&output);
    let ok = status.success();
    Ok(json!({
        "ok": ok,
        "passed": report.passed,
        "failed": report
            .failed
            .iter()
            .map(|(name, report)| json!({ "name": name, "report": report }))
            .collect::<Vec<_>>(),
        "output": output,
    }))
}

/// Runs a command, killing it at the limit: what it wrote to standard
/// output and error, and its status, none if it was killed.
fn run_bounded(
    mut command: Command,
    limit: Duration,
) -> Result<(String, Option<std::process::ExitStatus>), String> {
    let mut child = command
        .spawn()
        .map_err(|e| format!("cannot start crag test: {e}"))?;
    let reader = |pipe: Option<Box<dyn Read + Send>>| {
        std::thread::spawn(move || {
            let mut bytes = Vec::new();
            if let Some(mut pipe) = pipe {
                let _ = pipe.read_to_end(&mut bytes);
            }
            bytes
        })
    };
    let out = reader(
        child
            .stdout
            .take()
            .map(|p| Box::new(p) as Box<dyn Read + Send>),
    );
    let err = reader(
        child
            .stderr
            .take()
            .map(|p| Box::new(p) as Box<dyn Read + Send>),
    );
    let deadline = Instant::now() + limit;
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break Some(status),
            Ok(None) if Instant::now() >= deadline => {
                let _ = child.kill();
                let _ = child.wait();
                break None;
            }
            Ok(None) => std::thread::sleep(Duration::from_millis(20)),
            Err(e) => return Err(format!("cannot wait for crag test: {e}")),
        }
    };
    let mut text = String::from_utf8_lossy(&out.join().unwrap_or_default()).into_owned();
    text += &String::from_utf8_lossy(&err.join().unwrap_or_default());
    Ok((text, status))
}

/// What `crag test` printed, by test.
#[derive(Debug, Default, PartialEq, Eq)]
struct TestLines {
    passed: Vec<String>,
    /// Each failed test with its report.
    failed: Vec<(String, String)>,
}

/// Reads `crag test`'s output: a line per test, `test <name> ... ok` or
/// `... FAILED`, then each failure's report under `<name>:`, then the
/// counts.
fn parse_test_output(output: &str) -> TestLines {
    let mut lines = TestLines::default();
    let mut failed = Vec::new();
    for line in output.lines() {
        let Some(rest) = line.strip_prefix("test ") else {
            continue;
        };
        if let Some(name) = rest.strip_suffix(" ... ok") {
            lines.passed.push(name.to_string());
        } else if let Some(name) = rest.strip_suffix(" ... FAILED") {
            failed.push(name.to_string());
        }
    }
    // The reports follow in the order of the failures.
    let starts: Vec<Option<usize>> = failed
        .iter()
        .map(|name| output.find(&format!("\n{name}:\n")))
        .collect();
    let end = output.rfind("\n\n").unwrap_or(output.len());
    for (i, name) in failed.iter().enumerate() {
        let report = starts[i].map_or(String::new(), |start| {
            let body = start + name.len() + 3;
            let stop = starts[i + 1..]
                .iter()
                .flatten()
                .next()
                .copied()
                .unwrap_or(end)
                .max(body);
            output[body..stop].trim_end().to_string()
        });
        lines.failed.push((name.clone(), report));
    }
    lines
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_the_output_of_crag_test() {
        let output = "test main.crag adds ... ok\n\
                      test main.crag splits ... FAILED\n\
                      test main.crag joins ... FAILED\n\
                      \nmain.crag splits:\nassertion failed: 1 == 2\n\
                      \nmain.crag joins:\ntrap: overflow\n  at join\n\
                      \n1 passed, 2 failed\n";
        let lines = parse_test_output(output);
        assert_eq!(lines.passed, ["main.crag adds"]);
        assert_eq!(
            lines.failed,
            [
                (
                    "main.crag splits".to_string(),
                    "assertion failed: 1 == 2".to_string()
                ),
                (
                    "main.crag joins".to_string(),
                    "trap: overflow\n  at join".to_string()
                ),
            ]
        );
    }
}
