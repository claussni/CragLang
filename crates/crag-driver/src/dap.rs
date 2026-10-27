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

//! The debug adapter (Specification §20.8.7): `crag dap` speaks the Debug
//! Adapter Protocol on standard input and output, so editors debug the app
//! without a plugin.
//!
//! `launch` loads the project, starts the session and the app; the
//! breakpoints an editor sets arrive before or after and apply either way.
//! DAP threads are the app's stopped tasks, numbered from 2, and thread 1
//! is the app itself. The adapter looks for newly stopped tasks every
//! 20 ms while the app runs and reports each with a `stopped` event; it
//! reports the app's end with `exited` and `terminated`.
//!
//! The adapter ends at `disconnect` or when its input ends, stopping the
//! app.

use std::collections::HashMap;
use std::io::{BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::time::Duration;

use crag_session::ImageCommand;
use serde_json::{Value, json};

use crate::debug::{Pause, Resume};
use crate::lsp::rpc;
use crate::project::Project;
use crate::scratch::Scratch;

/// How often the adapter looks at the app while it runs.
const POLL: Duration = Duration::from_millis(20);

/// The thread that stands for the app, which has no task of its own here.
const APP_THREAD: i64 = 1;

struct Adapter {
    out: Box<dyn Write + Send>,
    seq: i64,
    command: ImageCommand,
    project: Option<Project>,
    scratch: Option<Scratch>,
    root: Option<PathBuf>,
    /// The breakpoints by file, as the project shows it, and line.
    breakpoints: HashMap<String, Vec<u32>>,
    /// DAP thread numbers of tasks, and the tasks reported stopped.
    threads: HashMap<u64, i64>,
    reported: Vec<u64>,
    /// The reason the next stop of a task is reported with.
    reasons: HashMap<u64, &'static str>,
    /// Frames handed out: the task, and whether it is the top frame.
    frames: HashMap<i64, (u64, bool)>,
    next_frame: i64,
}

/// Runs the adapter until `disconnect` or the end of the input; the exit
/// status. Images are started with `command`.
pub fn serve(
    input: impl Read + Send + 'static,
    output: impl Write + Send + 'static,
    command: ImageCommand,
) -> u8 {
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let mut input = BufReader::new(input);
        loop {
            match rpc::read(&mut input) {
                Ok(Some(message)) => {
                    if tx.send(message).is_err() {
                        return;
                    }
                }
                Ok(None) | Err(_) => return,
            }
        }
    });
    let mut adapter = Adapter {
        out: Box::new(output),
        seq: 1,
        command,
        project: None,
        scratch: None,
        root: None,
        breakpoints: HashMap::new(),
        threads: HashMap::new(),
        reported: Vec::new(),
        reasons: HashMap::new(),
        frames: HashMap::new(),
        next_frame: 1,
    };
    loop {
        let message = if adapter.scratch.is_some() {
            match rx.recv_timeout(POLL) {
                Ok(message) => Some(message),
                Err(mpsc::RecvTimeoutError::Timeout) => None,
                Err(mpsc::RecvTimeoutError::Disconnected) => break,
            }
        } else {
            match rx.recv() {
                Ok(message) => Some(message),
                Err(_) => break,
            }
        };
        match message {
            Some(message) => {
                if adapter.handle(&message) {
                    adapter.end();
                    return 0;
                }
            }
            None => adapter.poll(),
        }
    }
    adapter.end();
    0
}

impl Adapter {
    fn send(&mut self, mut message: Value) {
        message["seq"] = json!(self.seq);
        self.seq += 1;
        // A client that went away is noticed on the input side.
        let _ = rpc::write(&mut *self.out, &message);
    }

    fn event(&mut self, event: &str, body: Value) {
        self.send(json!({"type": "event", "event": event, "body": body}));
    }

    fn respond(&mut self, request: &Value, result: Result<Value, String>) {
        let mut response = json!({
            "type": "response",
            "request_seq": request["seq"],
            "command": request["command"],
            "success": result.is_ok(),
        });
        match result {
            Ok(body) => response["body"] = body,
            Err(message) => response["message"] = json!(message),
        }
        self.send(response);
    }

    /// Handles a request; true when the adapter is to end.
    fn handle(&mut self, request: &Value) -> bool {
        if request["type"] != "request" {
            return false;
        }
        let command = request["command"].as_str().unwrap_or_default().to_string();
        let args = request.get("arguments").cloned().unwrap_or(Value::Null);
        let result = match command.as_str() {
            "initialize" => {
                let capabilities = json!({
                    "supportsConfigurationDoneRequest": true,
                    "supportsTerminateRequest": true,
                });
                self.respond(request, Ok(capabilities));
                self.event("initialized", json!({}));
                return false;
            }
            "launch" => self.launch(&args),
            "attach" => Err("attaching to a running session is not supported yet".into()),
            "setBreakpoints" => self.set_breakpoints(&args),
            "setExceptionBreakpoints" => Ok(json!({"breakpoints": []})),
            "setFunctionBreakpoints" => Ok(json!({"breakpoints": []})),
            "configurationDone" => Ok(json!({})),
            "threads" => self.threads(),
            "stackTrace" => self.stack_trace(&args),
            "scopes" => self.scopes(&args),
            "variables" => self.variables(&args),
            "continue" => self.go_on(&args, Resume::Continue, "breakpoint"),
            "next" => self.go_on(&args, Resume::Over, "step"),
            "stepIn" => self.go_on(&args, Resume::Into, "step"),
            "stepOut" => self.go_on(&args, Resume::Out, "step"),
            "disconnect" | "terminate" => {
                self.stop_app();
                self.respond(request, Ok(json!({})));
                if command == "terminate" {
                    self.event("terminated", json!({}));
                    return false;
                }
                return true;
            }
            other => Err(format!("`{other}` is not supported")),
        };
        self.respond(request, result);
        false
    }

    fn launch(&mut self, args: &Value) -> Result<Value, String> {
        let root = args["project"]
            .as_str()
            .or_else(|| args["cwd"].as_str())
            .map_or_else(|| PathBuf::from("."), PathBuf::from);
        let project = Project::load(&root)?;
        self.root = Some(root.canonicalize().unwrap_or_else(|_| root.clone()));
        // Breakpoints set before were kept by the paths given.
        let before = std::mem::take(&mut self.breakpoints);
        for (path, lines) in before {
            let file = self.shown(&path);
            self.breakpoints.insert(file, lines);
        }
        let mut scratch = Scratch::start(self.command.clone())
            .map_err(|e| format!("cannot start the session: {e}"))?;
        let breakpoints = self.all_breakpoints();
        scratch.set_breakpoints(&project, &breakpoints)?;
        scratch.start_app(&project)?;
        self.project = Some(project);
        self.scratch = Some(scratch);
        self.event("process", json!({"name": "app", "startMethod": "launch"}));
        Ok(json!({}))
    }

    fn all_breakpoints(&self) -> Vec<(String, u32)> {
        let mut all: Vec<(String, u32)> = self
            .breakpoints
            .iter()
            .flat_map(|(file, lines)| lines.iter().map(move |&l| (file.clone(), l)))
            .collect();
        all.sort();
        all
    }

    /// A source path as the project shows its files: relative to its root.
    fn shown(&self, path: &str) -> String {
        let path = Path::new(path);
        let full = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
        match &self.root {
            Some(root) => full
                .strip_prefix(root)
                .map_or_else(|_| path.display().to_string(), |p| p.display().to_string()),
            None => path.display().to_string(),
        }
    }

    fn set_breakpoints(&mut self, args: &Value) -> Result<Value, String> {
        let path = args["source"]["path"]
            .as_str()
            .ok_or("a source without a path")?;
        let lines: Vec<u32> = args["breakpoints"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(|b| b["line"].as_u64().map(|l| l as u32))
            .collect();
        // Before `launch` the root is not known yet; the path is kept as
        // given and made relative then.
        let file = self.shown(path);
        self.breakpoints.insert(file.clone(), lines.clone());
        let all = self.all_breakpoints();
        let placed = match (&mut self.scratch, &self.project) {
            (Some(scratch), Some(project)) => scratch.set_breakpoints(project, &all)?,
            _ => vec![1; all.len()],
        };
        let breakpoints: Vec<Value> = lines
            .iter()
            .map(|&line| {
                let k = all.iter().position(|b| *b == (file.clone(), line));
                let verified = k.and_then(|k| placed.get(k)).is_some_and(|&n| n > 0);
                json!({"verified": verified, "line": line})
            })
            .collect();
        Ok(json!({"breakpoints": breakpoints}))
    }

    fn pauses(&mut self) -> Vec<Pause> {
        match (&mut self.scratch, &self.project) {
            (Some(scratch), Some(project)) => scratch.pauses(project).unwrap_or_default(),
            _ => Vec::new(),
        }
    }

    fn thread_of(&mut self, task: u64) -> i64 {
        let next = self.threads.len() as i64 + 2;
        *self.threads.entry(task).or_insert(next)
    }

    fn task_of(&self, thread: i64) -> Option<u64> {
        self.threads
            .iter()
            .find(|&(_, &t)| t == thread)
            .map(|(&task, _)| task)
    }

    fn threads(&mut self) -> Result<Value, String> {
        let mut threads = vec![json!({"id": APP_THREAD, "name": "app"})];
        for pause in self.pauses() {
            let id = self.thread_of(pause.task);
            threads.push(json!({"id": id, "name": format!("task in {}", pause.function)}));
        }
        Ok(json!({"threads": threads}))
    }

    fn paused_task(&mut self, args: &Value) -> Result<Pause, String> {
        let thread = args["threadId"].as_i64().ok_or("no threadId")?;
        let task = self.task_of(thread).ok_or("that thread is not stopped")?;
        self.pauses()
            .into_iter()
            .find(|p| p.task == task)
            .ok_or_else(|| "that thread is not stopped".into())
    }

    fn stack_trace(&mut self, args: &Value) -> Result<Value, String> {
        let pause = self.paused_task(args)?;
        let root = self.root.clone().unwrap_or_default();
        let mut frames = Vec::new();
        let id = self.next_frame;
        self.next_frame += 1;
        self.frames.insert(id, (pause.task, true));
        frames.push(json!({
            "id": id,
            "name": pause.function,
            "source": {"name": pause.file, "path": root.join(&pause.file).display().to_string()},
            "line": pause.line,
            "column": 1,
        }));
        // The frames below are known by their functions.
        for caller in &pause.callers {
            let id = self.next_frame;
            self.next_frame += 1;
            self.frames.insert(id, (pause.task, false));
            frames.push(json!({
                "id": id,
                "name": caller,
                "line": 0,
                "column": 0,
                "presentationHint": "subtle",
            }));
        }
        Ok(json!({"stackFrames": frames, "totalFrames": frames.len()}))
    }

    fn scopes(&mut self, args: &Value) -> Result<Value, String> {
        let frame = args["frameId"].as_i64().ok_or("no frameId")?;
        Ok(match self.frames.get(&frame) {
            Some(&(_, true)) => {
                json!({"scopes": [{"name": "Locals", "variablesReference": frame, "expensive": false}]})
            }
            _ => json!({"scopes": []}),
        })
    }

    fn variables(&mut self, args: &Value) -> Result<Value, String> {
        let frame = args["variablesReference"]
            .as_i64()
            .ok_or("no variablesReference")?;
        let &(task, _) = self.frames.get(&frame).ok_or("no such variables")?;
        let scratch = self.scratch.as_mut().ok_or("the app does not run")?;
        let locals = scratch.locals(task)?;
        let variables: Vec<Value> = locals
            .into_iter()
            .map(|(name, value)| json!({"name": name, "value": value, "variablesReference": 0}))
            .collect();
        Ok(json!({"variables": variables}))
    }

    fn go_on(&mut self, args: &Value, how: Resume, reason: &'static str) -> Result<Value, String> {
        let pause = self.paused_task(args)?;
        let scratch = self.scratch.as_mut().ok_or("the app does not run")?;
        scratch.resume(pause.task, how)?;
        self.reported.retain(|&t| t != pause.task);
        self.reasons.insert(pause.task, reason);
        self.frames.retain(|_, (t, _)| *t != pause.task);
        Ok(json!({"allThreadsContinued": false}))
    }

    /// Reports newly stopped tasks, and the app's end.
    fn poll(&mut self) {
        let pauses = self.pauses();
        for pause in pauses {
            if self.reported.contains(&pause.task) {
                continue;
            }
            self.reported.push(pause.task);
            let thread = self.thread_of(pause.task);
            let reason = self.reasons.remove(&pause.task).unwrap_or("breakpoint");
            self.event(
                "stopped",
                json!({"reason": reason, "threadId": thread, "allThreadsStopped": false}),
            );
        }
        let ended = match (&mut self.scratch, &self.project) {
            (Some(scratch), Some(project)) => scratch.app_status(project).ok().flatten(),
            _ => None,
        };
        if let Some(ended) = ended {
            self.event(
                "output",
                json!({"category": "console", "output": format!("{ended}\n")}),
            );
            self.event("exited", json!({"exitCode": 0}));
            self.event("terminated", json!({}));
            self.scratch = None;
        }
    }

    fn stop_app(&mut self) {
        if let Some(scratch) = &mut self.scratch {
            let _ = scratch.stop_app();
        }
        self.scratch = None;
    }

    fn end(&mut self) {
        self.stop_app();
    }
}
