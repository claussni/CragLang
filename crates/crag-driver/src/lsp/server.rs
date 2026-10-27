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

//! The server's state and the dispatch of messages.

use std::collections::HashMap;
use std::io::{BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use crag_db::{Db, catch_cancelled};
use crag_hir::{ModuleId, Program};
use serde_json::{Value, json};

use super::analysis::{self, FileEntry, Files, Target};
use super::rpc::{self, code};
use super::text::{self, Encoding};
use crate::diagnostics::{import_cycles, module_diagnostics};
use crate::project::Project;

/// Where messages go: one writer shared by the main thread and the
/// request threads.
#[derive(Clone)]
struct Out(Arc<Mutex<Box<dyn Write + Send>>>);

impl Out {
    fn send(&self, message: Value) {
        let mut output = self.0.lock().unwrap_or_else(|e| e.into_inner());
        // A client that went away is noticed on the input side.
        let _ = rpc::write(&mut **output, &message);
    }

    fn respond(&self, id: &Value, result: Value) {
        self.send(json!({"jsonrpc": "2.0", "id": id, "result": result}));
    }

    fn error(&self, id: &Value, code: i64, message: &str) {
        self.send(json!({"jsonrpc": "2.0", "id": id, "error": {"code": code, "message": message}}));
    }

    fn notify(&self, method: &str, params: Value) {
        self.send(json!({"jsonrpc": "2.0", "method": method, "params": params}));
    }
}

/// An open document.
struct Document {
    module: ModuleId,
    text: String,
}

/// The requests being answered, with the flag that cancels each.
type RequestTable = Arc<Mutex<HashMap<String, Arc<AtomicBool>>>>;

struct Server {
    out: Out,
    project: Project,
    encoding: Encoding,
    /// Open documents by URI.
    documents: HashMap<String, Document>,
    requests: RequestTable,
    /// Counts edits, so diagnostics of an older state are not published.
    generation: Arc<AtomicU64>,
    /// The diagnostics last published, by URI.
    published: Arc<Mutex<HashMap<String, Value>>>,
    initialized: bool,
    shutdown: bool,
    /// When the diagnostics are to be published: a short pause after the
    /// last edit, since typing comes in bursts.
    diagnose_at: Option<Instant>,
}

/// The pause after an edit before diagnostics are computed.
const DIAGNOSTICS_PAUSE: Duration = Duration::from_millis(40);

/// How long `shutdown` waits for the requests in flight.
const SHUTDOWN_WAIT: Duration = Duration::from_secs(5);

/// Runs the server until `exit` or the end of the input; the exit status.
pub fn serve(input: impl Read + Send + 'static, output: impl Write + Send + 'static) -> u8 {
    let out = Out(Arc::new(Mutex::new(Box::new(output))));
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let mut input = BufReader::new(input);
        loop {
            match rpc::read(&mut input) {
                Ok(Some(message)) => {
                    if tx.send(Ok(message)).is_err() {
                        return;
                    }
                }
                Ok(None) => return,
                Err(e) => {
                    let _ = tx.send(Err(e));
                    return;
                }
            }
        }
    });
    let mut server = Server {
        out,
        project: Project::bare(),
        encoding: Encoding::Utf16,
        documents: HashMap::new(),
        requests: Arc::default(),
        generation: Arc::default(),
        published: Arc::default(),
        initialized: false,
        shutdown: false,
        diagnose_at: None,
    };
    loop {
        let message = match server.diagnose_at {
            Some(at) => match rx.recv_timeout(at.saturating_duration_since(Instant::now())) {
                Ok(message) => message,
                Err(mpsc::RecvTimeoutError::Timeout) => {
                    server.diagnose_at = None;
                    server.publish_diagnostics();
                    continue;
                }
                Err(mpsc::RecvTimeoutError::Disconnected) => return 1,
            },
            // The reader ends with the input, which ends the loop.
            None => match rx.recv() {
                Ok(message) => message,
                Err(_) => return 1,
            },
        };
        let message = match message {
            Ok(message) => message,
            Err(e) => {
                server.out.notify(
                    "window/logMessage",
                    json!({"type": 1, "message": format!("crag lsp: {e}")}),
                );
                return 1;
            }
        };
        if let Some(status) = server.handle(message) {
            return status;
        }
    }
}

fn str_param<'a>(params: &'a Value, path: &[&str]) -> Option<&'a str> {
    let mut value = params;
    for key in path {
        value = value.get(key)?;
    }
    value.as_str()
}

/// A file URI's path, with percent escapes decoded.
fn uri_path(uri: &str) -> Option<PathBuf> {
    let rest = uri.strip_prefix("file://")?;
    let rest = rest.strip_prefix("localhost").unwrap_or(rest);
    let bytes = rest.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' && i + 2 < bytes.len() {
            let hex = std::str::from_utf8(&bytes[i + 1..i + 3]).ok()?;
            out.push(u8::from_str_radix(hex, 16).ok()?);
            i += 3;
        } else {
            out.push(bytes[i]);
            i += 1;
        }
    }
    Some(PathBuf::from(String::from_utf8(out).ok()?))
}

/// The URI of a path, escaping what a URI cannot hold.
fn path_uri(path: &Path) -> String {
    let mut out = String::from("file://");
    for b in path.to_string_lossy().bytes() {
        if b.is_ascii_alphanumeric() || b"/-_.~".contains(&b) {
            out.push(b as char);
        } else {
            out.push_str(&format!("%{b:02X}"));
        }
    }
    out
}

/// Where the bundled `std` modules are written, so that a definition in
/// them has a file to open: `$CRAG_HOME/std` or `~/.crag/std` (§20.8.3).
fn std_dir() -> Option<PathBuf> {
    let home = std::env::var_os("CRAG_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".crag")))?;
    Some(home.join("std"))
}

impl Server {
    /// Handles a message; the exit status once the server is to stop.
    fn handle(&mut self, message: Value) -> Option<u8> {
        let method = message
            .get("method")
            .and_then(Value::as_str)
            .map(str::to_string);
        let id = message.get("id").cloned();
        let params = message.get("params").cloned().unwrap_or(Value::Null);
        let Some(method) = method else {
            // A response to a request of ours; the server sends none.
            return None;
        };
        match id {
            Some(id) => self.request(id, &method, params),
            None => return self.notification(&method, params),
        }
        None
    }

    fn notification(&mut self, method: &str, params: Value) -> Option<u8> {
        match method {
            "exit" => return Some(if self.shutdown { 0 } else { 1 }),
            "initialized" => self.diagnose(),
            "$/cancelRequest" => {
                let key = params.get("id").map(Value::to_string).unwrap_or_default();
                if let Some(flag) = self.requests.lock().unwrap().get(&key) {
                    flag.store(true, Ordering::Relaxed);
                }
            }
            _ if !self.initialized => {}
            "textDocument/didOpen" => {
                let doc = &params["textDocument"];
                if let (Some(uri), Some(text)) =
                    (str_param(doc, &["uri"]), str_param(doc, &["text"]))
                {
                    self.open(uri, text.to_string());
                    self.diagnose();
                }
            }
            "textDocument/didChange" => {
                // A change to a document that is not open is ignored.
                let uri = str_param(&params, &["textDocument", "uri"])?;
                let document = self.documents.get_mut(uri)?;
                let mut text = document.text.clone();
                for change in params["contentChanges"].as_array().into_iter().flatten() {
                    text::apply_change(&mut text, change, self.encoding)?;
                }
                let module = document.module;
                document.text = text.clone();
                self.set_text(module, text);
                self.diagnose();
            }
            "textDocument/didClose" => {
                if let Some(uri) = str_param(&params, &["textDocument", "uri"]) {
                    self.close(uri);
                    self.diagnose();
                }
            }
            "workspace/didChangeWatchedFiles" => {
                for change in params["changes"].as_array().into_iter().flatten() {
                    if let Some(uri) = str_param(change, &["uri"])
                        && !self.documents.contains_key(uri)
                    {
                        self.reload_from_disk(uri);
                    }
                }
                self.diagnose();
            }
            _ => {}
        }
        None
    }

    fn request(&mut self, id: Value, method: &str, params: Value) {
        match method {
            "initialize" => {
                self.initialize(&params);
                let result = json!({
                    "capabilities": {
                        "positionEncoding": self.encoding.name(),
                        "textDocumentSync": {"openClose": true, "change": 2, "save": false},
                        "hoverProvider": true,
                        "definitionProvider": true,
                        "referencesProvider": true,
                        "documentHighlightProvider": true,
                        "renameProvider": {"prepareProvider": true},
                        "completionProvider": {"triggerCharacters": ["."]},
                        "documentFormattingProvider": true,
                        "documentSymbolProvider": true,
                    },
                    "serverInfo": {"name": "crag", "version": env!("CARGO_PKG_VERSION")},
                });
                self.initialized = true;
                self.out.respond(&id, result);
            }
            _ if !self.initialized => self.out.error(
                &id,
                code::SERVER_NOT_INITIALIZED,
                "the server is not initialized",
            ),
            "shutdown" => {
                self.shutdown = true;
                // The requests in flight are answered first, within a bound.
                let deadline = Instant::now() + SHUTDOWN_WAIT;
                while !self.requests.lock().unwrap().is_empty() && Instant::now() < deadline {
                    std::thread::sleep(Duration::from_millis(5));
                }
                self.out.respond(&id, Value::Null);
            }
            "textDocument/hover"
            | "textDocument/definition"
            | "textDocument/references"
            | "textDocument/documentHighlight"
            | "textDocument/prepareRename"
            | "textDocument/rename"
            | "textDocument/completion"
            | "textDocument/formatting"
            | "textDocument/documentSymbol" => self.spawn(id, method.to_string(), params),
            _ => self.out.error(
                &id,
                code::METHOD_NOT_FOUND,
                &format!("unknown method `{method}`"),
            ),
        }
    }

    fn initialize(&mut self, params: &Value) {
        let encodings = params["capabilities"]["general"]["positionEncodings"].as_array();
        if encodings.is_some_and(|e| e.iter().any(|e| e == "utf-8")) {
            self.encoding = Encoding::Utf8;
        }
        let root = str_param(params, &["rootUri"])
            .and_then(uri_path)
            .or_else(|| str_param(params, &["rootPath"]).map(PathBuf::from))
            .or_else(|| {
                params["workspaceFolders"]
                    .as_array()
                    .and_then(|f| f.first())
                    .and_then(|f| str_param(f, &["uri"]))
                    .and_then(uri_path)
            });
        if let Some(root) = root.filter(|r| r.join("package.crag").exists()) {
            match Project::load(&root) {
                Ok(project) => self.project = project,
                Err(e) => self.out.notify(
                    "window/showMessage",
                    json!({"type": 1, "message": format!("crag: {e}")}),
                ),
            }
        }
    }

    /// The module of a file: the project's, or a new one for a file
    /// outside it.
    fn module_of(&mut self, uri: &str, text: &str) -> ModuleId {
        let path = uri_path(uri);
        if let (Some(path), Some(root)) = (&path, &self.project.root) {
            let root = root.canonicalize().unwrap_or_else(|_| root.clone());
            let full = path.canonicalize().unwrap_or_else(|_| path.clone());
            if let Ok(relative) = full.strip_prefix(&root) {
                let shown = relative.display().to_string();
                if let Some(file) = self.project.own().iter().find(|f| f.shown == shown) {
                    return file.module;
                }
                let segments: Vec<String> = relative
                    .with_extension("")
                    .components()
                    .map(|c| c.as_os_str().to_string_lossy().into_owned())
                    .collect();
                let name = format!("{}.{}", self.project.package, segments.join("."));
                return self.project.add_module(&name, &shown, text.to_string());
            }
        }
        if let Some(module) = self.project.module(&format!("editor.{uri}")) {
            return module;
        }
        let shown = path.map_or_else(|| uri.to_string(), |p| p.display().to_string());
        self.project
            .add_module(&format!("editor.{uri}"), &shown, text.to_string())
    }

    fn open(&mut self, uri: &str, text: String) {
        let module = self.module_of(uri, &text);
        self.set_text(module, text.clone());
        self.documents
            .insert(uri.to_string(), Document { module, text });
    }

    fn close(&mut self, uri: &str) {
        if let Some(document) = self.documents.remove(uri) {
            match uri_path(uri).and_then(|p| std::fs::read_to_string(p).ok()) {
                Some(text) => self.set_text(document.module, text),
                None => {
                    self.set_text(document.module, String::new());
                }
            }
        }
    }

    fn reload_from_disk(&mut self, uri: &str) {
        let text = uri_path(uri)
            .and_then(|p| std::fs::read_to_string(p).ok())
            .unwrap_or_default();
        let module = self.module_of(uri, &text);
        self.set_text(module, text);
    }

    /// Changes a module's text. Queries on older snapshots are cancelled,
    /// and this waits until they let go of them.
    fn set_text(&mut self, module: ModuleId, text: String) {
        self.generation.fetch_add(1, Ordering::SeqCst);
        if self.project.source(module) != text {
            self.project.set_source(module, text);
        }
    }

    /// Where every module is, for a request thread.
    fn files(&self) -> Files {
        let db = &self.project.db;
        let root = self.project.root.clone();
        let std = std_dir();
        let entries = self
            .project
            .files
            .iter()
            .map(|file| {
                let path = file.module.path(db);
                let open = self.documents.iter().find(|(_, d)| d.module == file.module);
                if let Some((uri, _)) = open {
                    return FileEntry {
                        module: file.module,
                        uri: uri.clone(),
                        editable: true,
                    };
                }
                if let Some(rest) = path.strip_prefix("std.") {
                    let uri = std
                        .as_ref()
                        .map(|d| path_uri(&d.join(format!("{rest}.crag"))));
                    return FileEntry {
                        module: file.module,
                        uri: uri.unwrap_or_default(),
                        editable: false,
                    };
                }
                let uri = match &root {
                    Some(root) if !path.starts_with("editor.") => path_uri(&root.join(&file.shown)),
                    _ => path.strip_prefix("editor.").unwrap_or(path).to_string(),
                };
                FileEntry {
                    module: file.module,
                    uri,
                    editable: true,
                }
            })
            .collect();
        Files {
            entries,
            package: (!self.project.package.is_empty()).then(|| self.project.package.clone()),
        }
    }

    /// Answers a request on a thread of its own.
    fn spawn(&mut self, id: Value, method: String, params: Value) {
        let uri = str_param(&params, &["textDocument", "uri"])
            .unwrap_or_default()
            .to_string();
        let Some(document) = self.documents.get(&uri) else {
            self.out
                .error(&id, code::INVALID_PARAMS, "the document is not open");
            return;
        };
        let request = Request {
            module: document.module,
            text: document.text.clone(),
            encoding: self.encoding,
            files: self.files(),
            program: self.project.program,
        };
        let snapshot = self.project.db.snapshot();
        let cancelled = Arc::new(AtomicBool::new(false));
        let key = id.to_string();
        self.requests
            .lock()
            .unwrap()
            .insert(key.clone(), cancelled.clone());
        let (out, requests) = (self.out.clone(), self.requests.clone());
        std::thread::spawn(move || {
            let answer = catch_cancelled(|| request.answer(snapshot.db(), &method, &params));
            drop(snapshot);
            match answer {
                _ if cancelled.load(Ordering::Relaxed) => {
                    out.error(&id, code::REQUEST_CANCELLED, "the request was cancelled")
                }
                Ok(Ok(result)) => out.respond(&id, result),
                Ok(Err((code, message))) => out.error(&id, code, &message),
                Err(_) => out.error(&id, code::CONTENT_MODIFIED, "the document changed"),
            }
            // Only once answered, so `shutdown` waits for it.
            requests.lock().unwrap().remove(&key);
        });
    }

    /// Has the diagnostics published after a pause.
    fn diagnose(&mut self) {
        if self.initialized {
            self.diagnose_at = Some(Instant::now() + DIAGNOSTICS_PAUSE);
        }
    }

    /// Publishes the diagnostics of the project's modules from a thread of
    /// its own, unless an edit comes first.
    fn publish_diagnostics(&mut self) {
        let generation = self.generation.load(Ordering::SeqCst);
        let snapshot = self.project.db.snapshot();
        let files = self.files();
        let program = self.project.program;
        let std_count = self.project.files.len() - self.project.own().len();
        let (out, current, published) = (
            self.out.clone(),
            self.generation.clone(),
            self.published.clone(),
        );
        let encoding = self.encoding;
        std::thread::spawn(move || {
            let result = catch_cancelled(|| {
                let db = snapshot.db();
                let mut by_module: Vec<(String, Value)> = Vec::new();
                let cycles = import_cycles(db, program);
                for entry in files.entries.iter().skip(std_count) {
                    let source = entry.module.file(db).text(db);
                    let mut diagnostics: Vec<Value> = module_diagnostics(db, program, entry.module)
                        .into_iter()
                        .chain(cycles.iter().filter(|d| d.module == entry.module).cloned())
                        .map(|d| {
                            json!({
                                "range": text::json_range(source, d.range, encoding),
                                "severity": 1,
                                "source": "crag",
                                "message": d.message,
                            })
                        })
                        .collect();
                    diagnostics.dedup();
                    by_module.push((entry.uri.clone(), Value::Array(diagnostics)));
                }
                by_module
            });
            drop(snapshot);
            let Ok(by_module) = result else {
                return;
            };
            if current.load(Ordering::SeqCst) != generation {
                return;
            }
            let mut published = published.lock().unwrap();
            for (uri, diagnostics) in by_module {
                if published.get(&uri) == Some(&diagnostics) {
                    continue;
                }
                out.notify(
                    "textDocument/publishDiagnostics",
                    json!({"uri": uri, "diagnostics": diagnostics}),
                );
                published.insert(uri, diagnostics);
            }
        });
    }
}

/// What a request thread needs besides its snapshot.
struct Request {
    module: ModuleId,
    text: String,
    encoding: Encoding,
    files: Files,
    program: Program,
}

type Answer = Result<Value, (i64, String)>;

impl Request {
    fn offset(&self, params: &Value) -> Option<u32> {
        text::from_json(&self.text, params.get("position")?, self.encoding)
    }

    fn location(&self, db: &dyn Db, place: &analysis::Place) -> Option<Value> {
        let entry = self.files.uri(place.module)?;
        if entry.uri.is_empty() {
            return None;
        }
        let source = place.module.file(db).text(db);
        if !entry.editable {
            write_std(&entry.uri, source);
        }
        Some(json!({
            "uri": entry.uri,
            "range": text::json_range(source, place.range.clone(), self.encoding),
        }))
    }

    fn range(&self, range: std::ops::Range<u32>) -> Value {
        text::json_range(&self.text, range, self.encoding)
    }

    fn answer(&self, db: &dyn Db, method: &str, params: &Value) -> Answer {
        let (module, program) = (self.module, self.program);
        let offset = self.offset(params);
        Ok(match method {
            "textDocument/hover" => {
                let hover = offset.and_then(|o| analysis::hover(db, program, module, o));
                match hover {
                    Some((value, range)) => json!({
                        "contents": {"kind": "markdown", "value": value},
                        "range": self.range(range),
                    }),
                    None => Value::Null,
                }
            }
            "textDocument/definition" => {
                let target = offset.and_then(|o| analysis::target_at(db, program, module, o));
                let place = target.and_then(|(t, _)| analysis::definition(db, program, t));
                place
                    .and_then(|p| self.location(db, &p))
                    .unwrap_or(Value::Null)
            }
            "textDocument/references" => {
                let declaration = params["context"]["includeDeclaration"]
                    .as_bool()
                    .unwrap_or(true);
                let target = offset.and_then(|o| analysis::target_at(db, program, module, o));
                let places = target.map_or_else(Vec::new, |(t, _)| {
                    analysis::references(db, program, &self.files, t, declaration)
                });
                Value::Array(places.iter().filter_map(|p| self.location(db, p)).collect())
            }
            "textDocument/documentHighlight" => {
                let target = offset.and_then(|o| analysis::target_at(db, program, module, o));
                let places = target.map_or_else(Vec::new, |(t, _)| {
                    analysis::references(db, program, &self.files, t, true)
                });
                Value::Array(
                    places
                        .iter()
                        .filter(|p| p.module == module)
                        .map(|p| json!({"range": self.range(p.range.clone())}))
                        .collect(),
                )
            }
            "textDocument/prepareRename" => {
                let target = offset.and_then(|o| analysis::target_at(db, program, module, o));
                match target {
                    Some((t, range)) if self.renameable(db, t) => self.range(range),
                    Some(_) => {
                        return Err((
                            code::REQUEST_FAILED,
                            "this name is declared in std, which cannot change".into(),
                        ));
                    }
                    None => Value::Null,
                }
            }
            "textDocument/rename" => {
                let new_name = str_param(params, &["newName"]).unwrap_or_default();
                if !analysis::valid_name(new_name) {
                    return Err((code::REQUEST_FAILED, format!("`{new_name}` is not a name")));
                }
                let Some((target, _)) =
                    offset.and_then(|o| analysis::target_at(db, program, module, o))
                else {
                    return Err((
                        code::REQUEST_FAILED,
                        "there is no name here to rename".into(),
                    ));
                };
                if !self.renameable(db, target) {
                    return Err((
                        code::REQUEST_FAILED,
                        "this name is declared in std, which cannot change".into(),
                    ));
                }
                let mut changes: HashMap<String, Vec<Value>> = HashMap::new();
                for place in analysis::references(db, program, &self.files, target, true) {
                    let Some(entry) = self.files.uri(place.module) else {
                        continue;
                    };
                    if !entry.editable {
                        continue;
                    }
                    let source = if place.module == module {
                        self.text.as_str()
                    } else {
                        place.module.file(db).text(db)
                    };
                    changes.entry(entry.uri.clone()).or_default().push(json!({
                        "range": text::json_range(source, place.range, self.encoding),
                        "newText": new_name,
                    }));
                }
                json!({"changes": changes})
            }
            "textDocument/completion" => {
                let items =
                    offset.map_or_else(Vec::new, |o| analysis::completion(db, program, module, o));
                Value::Array(
                    items
                        .into_iter()
                        .map(|c| json!({"label": c.label, "kind": c.kind, "detail": c.detail}))
                        .collect(),
                )
            }
            "textDocument/formatting" => {
                let package = self.files.package.as_deref();
                match crag_fmt::format(&self.text, package) {
                    Ok(formatted) if formatted == self.text => json!([]),
                    Ok(formatted) => json!([{
                        "range": self.range(0..self.text.len() as u32),
                        "newText": formatted,
                    }]),
                    // A file that does not parse is formatted once it does.
                    Err(crag_fmt::FormatError::Syntax(_)) => json!([]),
                    Err(crag_fmt::FormatError::Changed) => {
                        return Err((
                            code::REQUEST_FAILED,
                            "the formatter would change what this file means; it is left alone"
                                .into(),
                        ));
                    }
                }
            }
            "textDocument/documentSymbol" => Value::Array(
                analysis::symbols(db, program, module)
                    .into_iter()
                    .map(|s| {
                        json!({
                            "name": s.name,
                            "kind": s.kind,
                            "range": self.range(s.range),
                            "selectionRange": self.range(s.selection),
                        })
                    })
                    .collect(),
            ),
            _ => return Err((code::METHOD_NOT_FOUND, format!("unknown method `{method}`"))),
        })
    }

    fn renameable(&self, db: &dyn Db, target: Target<'_>) -> bool {
        match target {
            Target::Local(..) => true,
            Target::Item(item) => self.files.uri(*item.module(db)).is_some_and(|e| e.editable),
        }
    }
}

/// Writes a bundled module where its URI points, if it is not there yet.
fn write_std(uri: &str, source: &str) {
    let Some(path) = uri_path(uri) else {
        return;
    };
    if std::fs::read_to_string(&path).ok().as_deref() == Some(source) {
        return;
    }
    if let Some(dir) = path.parent() {
        let _ = std::fs::create_dir_all(dir);
    }
    let _ = std::fs::write(&path, source);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uris_and_paths_convert_both_ways() {
        let path = Path::new("/home/a b/ü.crag");
        let uri = path_uri(path);
        assert_eq!(uri, "file:///home/a%20b/%C3%BC.crag");
        assert_eq!(uri_path(&uri).unwrap(), path);
    }
}
