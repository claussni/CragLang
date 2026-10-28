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

//! The REPL (Implementation Plan §11.6.2, Specification §17).
//!
//! The session's definitions are one module, `repl`, whose text is theirs,
//! one after another, so the queries that serve files serve the REPL and a
//! definition is a non-pub module function like any other. An input that
//! starts like a declaration adds its declarations; any other input is an
//! expression, which becomes the body of a function of the REPL's own,
//! `__input`, for as long as it is compiled and run in the scratch image.
//!
//! A name of the session is defined once; `:rebind` replaces its
//! definition, and the queries recheck what depends on it. An input with
//! errors changes nothing.

use std::collections::BTreeSet;

use crag_db::Setter;
use crag_hir::{ItemKind, ModuleId, Owner, SourceFile, item_tree, module_scope};
use crag_mir::{InstanceKey, Tier, mir};
use crag_session::RunResult;
use crag_syntax::{TokenKind, lex};
use crag_types::Ty;

use crate::debug::{Pause, Resume};
use crate::diagnostics::{check, render_at};
use crate::exec::Sources;
use crate::project::Project;
use crate::scratch::Scratch;

/// The name of the function an expression is the body of.
pub const INPUT: &str = "__input";

/// The path of the session's module.
const SESSION: &str = "repl";

const HELP: &str = "\
Enter a definition to add it to the session, or an expression to run it.
  :rebind <definition>  replace a definition of the session
  :start                start the project's app in the app image
  :reload               read changed files and swap their code into the app
  :status               how the app runs, and the files that differ from it
  :stop                 stop the app
  :break [file:line]    stop the app's tasks at a line; alone, list them
  :clear                remove every breakpoint
  :paused               the app's stopped tasks, numbered
  :locals [n]           the locals of stopped task n, the first by default
  :continue [n]         let stopped task n go on
  :step, :next, :out [n]  go on to the next statement: anywhere, in this
                        function or its caller, or in its caller
  :package add <package> [version], :package remove <package>,
  :package upgrade <package> [version: V], :package outdated, :package deps,
  :package sbom diff | regenerate, :package pack, :package publish <registry>
                        manage the project's packages, as the shell does
  :registry new <name> <folder> | add <name> <folder> | list | remove <name>
                        manage the registries of the settings
  :cd [directory]       go to another directory and the project in it, with
                        a fresh session; alone, show where the session runs
  :help                 show this
  :quit                 leave; so does Ctrl-D
An input continues on the next line until it is complete; an empty line
ends it as it is. Ctrl-C stops a run.
";

/// A REPL session: the project it runs in, the session's definitions and
/// the scratch image that runs its input.
pub struct Repl {
    project: Project,
    session: SessionModule,
    scratch: Scratch,
    /// The expression being run, while it is.
    input: Option<String>,
    /// The definition being added, whose errors are shown as the input's.
    fresh: Option<usize>,
    /// The text of each file as the app runs it, while it runs.
    app: Option<Vec<(String, String)>>,
    /// The type of the value the last input showed.
    shown_type: Option<String>,
}

/// The session's definitions, as the text of one module.
pub struct SessionModule {
    pub module: ModuleId,
    entries: Vec<Entry>,
}

/// One input that defined something: its text and the names it declares.
#[derive(Clone, Debug)]
struct Entry {
    text: String,
    names: Vec<String>,
}

/// Where the entries are in the session's text.
struct Placed {
    text: String,
    /// Each entry's start.
    starts: Vec<u32>,
    /// The start of the expression being run, inside its function.
    input: Option<u32>,
}

impl SessionModule {
    fn layout(&self, input: Option<&str>) -> Placed {
        let mut text = String::new();
        let mut starts = Vec::new();
        for entry in &self.entries {
            starts.push(text.len() as u32);
            text += &entry.text;
            text += "\n\n";
        }
        let input = input.map(|input| {
            text += &format!("fn {INPUT}() {{\n");
            let start = text.len() as u32;
            text += input;
            text += "\n}\n";
            start
        });
        Placed {
            text,
            starts,
            input,
        }
    }

    /// The definitions that name one of `names`, and those that name one of
    /// theirs, by their first names. A name is matched by its text, which
    /// no local binding may hide, since a local may not shadow a name of
    /// the module.
    fn dependents(&self, names: &[String]) -> Vec<String> {
        let mut changed: BTreeSet<String> = names.iter().cloned().collect();
        let mut out: Vec<usize> = Vec::new();
        loop {
            let found = self.entries.iter().enumerate().position(|(i, e)| {
                !out.contains(&i)
                    && !e.names.iter().any(|n| names.contains(n))
                    && mentions(&e.text, &changed)
            });
            let Some(i) = found else { break };
            out.push(i);
            changed.extend(self.entries[i].names.iter().cloned());
        }
        out.sort();
        out.iter()
            .filter_map(|&i| self.entries[i].names.first().cloned())
            .collect()
    }
}

/// Whether the text names one of the names. A name after `.` or `?.` is
/// a field, and one before `:` a label: a field's declaration, a
/// parameter or a named argument.
fn mentions(text: &str, names: &BTreeSet<String>) -> bool {
    let tokens = lex(text);
    tokens.iter().enumerate().any(|(i, t)| {
        let field = i > 0 && matches!(tokens[i - 1].kind, TokenKind::Dot | TokenKind::QuestionDot);
        let label = tokens
            .get(i + 1)
            .is_some_and(|n| n.kind == TokenKind::Colon);
        t.kind == TokenKind::Ident && !field && !label && names.contains(t.text(text))
    })
}

/// Whether an input declares something rather than being an expression:
/// it starts with a declaration's keyword.
pub fn is_definition(text: &str) -> bool {
    use TokenKind::*;
    let tokens = lex(text);
    matches!(
        tokens.first().map(|t| t.kind),
        Some(Fn | Type | Let | Import | Pub | Form | Embed | Test | Distinct | Opaque | Final)
    )
}

/// Whether an input is complete: the parser wants nothing more after its
/// end, so its first error, if any, is inside the input. A command is a
/// line.
pub fn is_complete(text: &str) -> bool {
    let text = text.trim_end();
    if text.is_empty() || text.starts_with(':') {
        return true;
    }
    let (source, end) = if is_definition(text) {
        (text.to_string(), text.len())
    } else {
        let source = format!("fn {INPUT}() {{\n{text}\n}}\n");
        let end = source.len() - 3;
        (source, end)
    };
    let (_, errors) = crag_syntax::parse(&source, &lex(&source));
    errors
        .iter()
        .map(|e| e.range.start as usize)
        .min()
        .is_none_or(|first| first < end)
}

/// What an input gave.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvalOutput {
    /// Definitions were added, or the input was empty; nothing to show.
    Nothing,
    /// `:rebind` replaced definitions; the session's definitions that
    /// depend on them are rechecked.
    Rebound {
        names: Vec<String>,
        dependents: Vec<String>,
    },
    /// An expression's value as the REPL shows it, or none for `()`.
    Value(Option<String>),
    /// A trap or Ctrl-C ended the run: the report.
    Stopped(String),
    /// What a command shows.
    Text(String),
    Quit,
}

impl EvalOutput {
    /// What the REPL prints.
    pub fn render(&self) -> String {
        match self {
            EvalOutput::Nothing | EvalOutput::Value(None) | EvalOutput::Quit => String::new(),
            EvalOutput::Rebound { names, dependents } => {
                let names = names.join(", ");
                match dependents.len() {
                    0 => format!("rebound {names}\n"),
                    1 => format!("rebound {names} (1 dependent: {})\n", dependents[0]),
                    n => format!(
                        "rebound {names} ({n} dependents: {})\n",
                        dependents.join(", ")
                    ),
                }
            }
            EvalOutput::Value(Some(value)) => format!("{value}\n"),
            EvalOutput::Stopped(text) | EvalOutput::Text(text) => text.clone(),
        }
    }
}

impl Repl {
    /// A session in the project, with the scratch image that runs it.
    pub fn new(mut project: Project, scratch: Scratch) -> Repl {
        let module = project.add_module(SESSION, SESSION, String::new());
        Repl {
            project,
            session: SessionModule {
                module,
                entries: Vec::new(),
            },
            scratch,
            input: None,
            fresh: None,
            app: None,
            shown_type: None,
        }
    }

    /// The project, to change its sources as an editor does.
    pub fn project_mut(&mut self) -> &mut Project {
        &mut self.project
    }

    /// What the scratch image and the app printed since the last call
    /// (Specification §15.6).
    pub fn take_printed(&mut self) -> String {
        String::from_utf8_lossy(&self.scratch.session.take_output()).into_owned()
    }

    /// The type of the value the last input showed.
    pub fn shown_type(&self) -> Option<&str> {
        self.shown_type.as_deref()
    }

    /// The text of a file as the app runs it, while it runs.
    pub fn app_text(&self, shown: &str) -> Option<&str> {
        self.app
            .as_ref()?
            .iter()
            .find(|(s, _)| s == shown)
            .map(|(_, text)| text.as_str())
    }

    /// The app's breakpoints, by file and line from one.
    pub fn breakpoints(&self) -> Vec<(String, u32)> {
        self.scratch.breakpoints().to_vec()
    }

    /// Sets the app's breakpoints: for each, how many functions have a
    /// statement there.
    pub fn set_breakpoints(&mut self, breakpoints: &[(String, u32)]) -> Result<Vec<usize>, String> {
        self.scratch.set_breakpoints(&self.project, breakpoints)
    }

    /// The app's stopped tasks.
    pub fn pauses(&mut self) -> Result<Vec<crate::debug::Pause>, String> {
        self.scratch.pauses(&self.project)
    }

    /// Whether the app runs.
    pub fn app_runs(&self) -> bool {
        self.scratch.app_runs()
    }

    pub fn project(&self) -> &Project {
        &self.project
    }

    pub fn scratch(&mut self) -> &mut Scratch {
        &mut self.scratch
    }

    /// Takes one input: a definition, an expression or a command. The
    /// errors come rendered, and leave the session as it was.
    pub fn eval_input(&mut self, text: &str) -> Result<EvalOutput, String> {
        self.shown_type = None;
        let text = text.trim();
        if text.is_empty() {
            return Ok(EvalOutput::Nothing);
        }
        if let Some(command) = text.strip_prefix(':') {
            return self.run_command(command);
        }
        if is_definition(text) {
            self.define(text).map(|_| EvalOutput::Nothing)
        } else {
            self.evaluate(text)
        }
    }

    /// A `:` command, without its colon.
    pub fn run_command(&mut self, command: &str) -> Result<EvalOutput, String> {
        let (name, rest) = command
            .split_once(char::is_whitespace)
            .unwrap_or((command, ""));
        match name {
            "quit" | "q" => Ok(EvalOutput::Quit),
            "help" => Ok(EvalOutput::Text(HELP.into())),
            "rebind" => self.rebind(rest.trim()),
            "start" => self.start_app(),
            "cd" => self.change_dir(rest.trim()),
            "reload" => self.reload(),
            "status" => self.status(),
            "break" => self.breakpoint(rest.trim()),
            "clear" => {
                self.scratch
                    .set_breakpoints(&self.project, &[])
                    .map_err(|e| format!("error: {e}\n"))?;
                Ok(EvalOutput::Text("no breakpoints\n".into()))
            }
            "paused" => self.paused(),
            "locals" => self.show_locals(rest.trim()),
            "continue" | "c" => self.go_on(rest.trim(), Resume::Continue),
            "step" | "s" => self.go_on(rest.trim(), Resume::Into),
            "next" | "n" => self.go_on(rest.trim(), Resume::Over),
            "out" => self.go_on(rest.trim(), Resume::Out),
            "package" => {
                let (verb, rest) = rest
                    .trim_start()
                    .split_once(char::is_whitespace)
                    .unwrap_or((rest.trim(), ""));
                if verb == "new" || !crate::packages::is_package_command(verb) {
                    return Err(
                        "error: :package takes add, remove, upgrade, outdated, deps, sbom, \
                         pack or publish\n"
                            .into(),
                    );
                }
                self.package_command(verb, rest)
            }
            "registry" => self.package_command("registry", rest),
            "stop" => {
                self.scratch
                    .stop_app()
                    .map_err(|e| format!("error: {e}\n"))?;
                self.app = None;
                Ok(EvalOutput::Text("the app stopped\n".into()))
            }
            _ => Err(format!(
                "error: there is no command :{name}; :help lists them\n"
            )),
        }
    }

    /// A command of the package manager (§20.6), with the REPL's
    /// arguments. After one that changed the packages, the session uses the
    /// new ones at once; the app gets them at its next reload.
    fn package_command(&mut self, name: &str, rest: &str) -> Result<EvalOutput, String> {
        let root = match (name, &self.project.root) {
            // Relative folders of the registries are the session's.
            ("registry", _) => std::env::current_dir().map_err(|e| format!("error: {e}\n"))?,
            (_, Some(root)) => root.clone(),
            (_, None) => return Err("error: package commands work in a project\n".into()),
        };
        let (spec, run) = crate::packages::command(name).expect("a package command");
        let args = crate::commands::Args::repl(rest, spec).map_err(|e| format!("error: {e}\n"))?;
        let mut out = Vec::new();
        let status = run(&root, &args, &mut out);
        let mut text = String::from_utf8_lossy(&out).into_owned();
        if status != 0 {
            return Err(text);
        }
        if crate::packages::changes_packages(name, &args) {
            self.project
                .reload_dependencies()
                .map_err(|e| format!("{text}error: {e}\n"))?;
            for warning in &self.project.warnings {
                text += &format!("warning: {warning}\n");
            }
        }
        Ok(EvalOutput::Text(text))
    }

    fn breakpoint(&mut self, place: &str) -> Result<EvalOutput, String> {
        let mut breakpoints = self.scratch.breakpoints().to_vec();
        if place.is_empty() {
            let mut out = String::new();
            for (file, line) in &breakpoints {
                out += &format!("{file}:{line}\n");
            }
            if out.is_empty() {
                out = "no breakpoints\n".into();
            }
            return Ok(EvalOutput::Text(out));
        }
        let (file, line) = place
            .rsplit_once(':')
            .and_then(|(f, l)| Some((f.to_string(), l.parse::<u32>().ok()?)))
            .ok_or("error: a breakpoint is file:line\n")?;
        if !breakpoints.contains(&(file.clone(), line)) {
            breakpoints.push((file.clone(), line));
        }
        let placed = self
            .scratch
            .set_breakpoints(&self.project, &breakpoints)
            .map_err(|e| format!("error: {e}\n"))?;
        let k = breakpoints
            .iter()
            .position(|b| *b == (file.clone(), line))
            .unwrap_or(0);
        Ok(EvalOutput::Text(match placed.get(k) {
            Some(0) | None if self.scratch.session().app().is_some() => {
                format!("{file}:{line} has no statement the app runs; it is kept for later\n")
            }
            _ => format!("breakpoint at {file}:{line}\n"),
        }))
    }

    /// The app's stopped tasks; an error when there are none.
    fn stopped(&mut self) -> Result<Vec<Pause>, String> {
        let pauses = self
            .scratch
            .pauses(&self.project)
            .map_err(|e| format!("error: {e}\n"))?;
        if pauses.is_empty() {
            return Err("no task is stopped\n".into());
        }
        Ok(pauses)
    }

    /// The stopped task an argument numbers, from one; the first by default.
    fn chosen(&mut self, arg: &str) -> Result<Pause, String> {
        let pauses = self.stopped()?;
        let n = match arg {
            "" => 1,
            n => n
                .parse::<usize>()
                .map_err(|_| format!("error: `{n}` numbers no task\n"))?,
        };
        pauses
            .get(n.wrapping_sub(1))
            .cloned()
            .ok_or_else(|| match pauses.len() {
                1 => "error: only 1 task is stopped\n".to_string(),
                n => format!("error: only {n} tasks are stopped\n"),
            })
    }

    fn paused(&mut self) -> Result<EvalOutput, String> {
        let mut out = String::new();
        for (i, p) in self.stopped()?.iter().enumerate() {
            out += &format!("{}: {} at {}:{}", i + 1, p.function, p.file, p.line);
            if !p.callers.is_empty() {
                out += &format!(", called from {}", p.callers.join(", "));
            }
            out += "\n";
        }
        Ok(EvalOutput::Text(out))
    }

    fn show_locals(&mut self, arg: &str) -> Result<EvalOutput, String> {
        let pause = self.chosen(arg)?;
        let locals = self
            .scratch
            .locals(pause.task)
            .map_err(|e| format!("error: {e}\n"))?;
        let mut out = String::new();
        for (name, value) in locals {
            out += &format!("{name} = {value}\n");
        }
        if out.is_empty() {
            out = "no locals hold values here\n".into();
        }
        Ok(EvalOutput::Text(out))
    }

    fn go_on(&mut self, arg: &str, how: Resume) -> Result<EvalOutput, String> {
        let pause = self.chosen(arg)?;
        self.scratch
            .resume(pause.task, how)
            .map_err(|e| format!("error: {e}\n"))?;
        if how == Resume::Continue {
            return Ok(EvalOutput::Nothing);
        }
        // Stepping ends at the next statement, which comes soon unless the
        // task waits; then `:paused` shows it later.
        let deadline = std::time::Instant::now() + std::time::Duration::from_millis(500);
        loop {
            let now = self
                .scratch
                .pauses(&self.project)
                .map_err(|e| format!("error: {e}\n"))?;
            if let Some(p) = now.iter().find(|p| p.task == pause.task) {
                return Ok(EvalOutput::Text(format!(
                    "{} at {}:{}\n",
                    p.function, p.file, p.line
                )));
            }
            if std::time::Instant::now() >= deadline {
                return Ok(EvalOutput::Text(
                    "the task runs on; :paused shows it once it stops\n".into(),
                ));
            }
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
    }

    /// `:cd [directory]`. Alone it tells the directory the session runs
    /// in. With a directory, relative to that one, the session moves
    /// there: it opens the project in it, or none if it has no
    /// `package.crag`, and starts afresh, with a new scratch image and
    /// without its definitions; a running app stops. The images and
    /// relative paths in programs then start from that directory.
    pub fn change_dir(&mut self, dir: &str) -> Result<EvalOutput, String> {
        let here = std::env::current_dir().map_err(|e| format!("error: {e}\n"))?;
        if dir.is_empty() {
            return Ok(EvalOutput::Text(format!("{}\n", here.display())));
        }
        let there = here
            .join(dir)
            .canonicalize()
            .map_err(|e| format!("error: cannot go to {dir}: {e}\n"))?;
        if !there.is_dir() {
            return Err(format!("error: {} is not a directory\n", there.display()));
        }
        let project = match there.join("package.crag").exists() {
            true => Project::load(&there).map_err(|e| format!("error: {e}\n"))?,
            false => Project::bare(),
        };
        std::env::set_current_dir(&there).map_err(|e| format!("error: {e}\n"))?;
        let command = self.scratch.session.command().clone();
        let scratch = match Scratch::start(command) {
            Ok(scratch) => scratch,
            Err(e) => {
                let _ = std::env::set_current_dir(&here);
                return Err(format!("error: cannot start the scratch image: {e}\n"));
            }
        };
        let mut text = format!("in {}", there.display());
        text += &match project.root {
            Some(_) => format!(", project {}\n", project.package),
            None => ", outside a project\n".to_string(),
        };
        for warning in &project.warnings {
            text += &format!("warning: {warning}\n");
        }
        let errors = check(&project).len();
        if errors > 0 {
            text += &format!(
                "the project has {errors} error{}\n",
                if errors == 1 { "" } else { "s" }
            );
        }
        *self = Repl::new(project, scratch);
        Ok(EvalOutput::Text(text))
    }

    fn start_app(&mut self) -> Result<EvalOutput, String> {
        if self.project.root.is_none() {
            return Err("error: the REPL runs outside a project, which has no app\n".into());
        }
        self.project.refresh();
        let shipment = self
            .scratch
            .start_app(&self.project)
            .map_err(|e| format!("error: {e}\n"))?;
        self.app = Some(self.project.texts());
        Ok(EvalOutput::Text(format!(
            "the app runs, with {} functions\n",
            shipment.functions
        )))
    }

    fn reload(&mut self) -> Result<EvalOutput, String> {
        let files = self.project.refresh();
        let shipment = self
            .scratch
            .reload(&self.project)
            .map_err(|e| format!("error: {e}\n"))?;
        self.app = Some(self.project.texts());
        let files = match files.as_slice() {
            [] => String::new(),
            files => format!(" from {}", files.join(", ")),
        };
        Ok(EvalOutput::Text(format!(
            "reloaded{files}: {} functions, {} values to compute again\n",
            shipment.functions, shipment.values
        )))
    }

    fn status(&mut self) -> Result<EvalOutput, String> {
        let mut out = match self.scratch.app_status(&self.project) {
            Ok(None) => "the app runs\n".to_string(),
            Ok(Some(ended)) => {
                self.app = None;
                format!("{}\n", ended.trim_end())
            }
            Err(e) => return Err(format!("error: {e}\n")),
        };
        if let (Some(app), Some(root)) = (&self.app, &self.project.root) {
            for (shown, text) in app {
                let disk = std::fs::read_to_string(root.join(shown)).unwrap_or_default();
                if disk != *text {
                    out += &format!("  {shown} changed since the app got its code\n");
                }
            }
        }
        Ok(EvalOutput::Text(out))
    }

    /// Replaces the definitions of the names a definition declares. Each
    /// must be defined in the session.
    pub fn rebind(&mut self, text: &str) -> Result<EvalOutput, String> {
        let names = self.declared(text)?;
        if names.is_empty() {
            return Err("error: :rebind takes a definition\n".into());
        }
        let old = self.session.entries.clone();
        // What it redefines goes, and another overload of a name stays; a
        // name defined once is replaced whatever its signature.
        let mut replaced = vec![false; old.len()];
        for name in &names {
            let defining: Vec<usize> = (0..old.len())
                .filter(|&i| old[i].names.iter().any(|n| n == name))
                .collect();
            let same: Vec<usize> = defining
                .iter()
                .copied()
                .filter(|&i| self.redefines(text, &old[i], name))
                .collect();
            let gone = match (same.is_empty(), defining.as_slice()) {
                (false, _) => same,
                (true, [one]) => vec![*one],
                (true, []) => {
                    return Err(format!(
                        "error: {name} is not defined in this session; define it without :rebind\n"
                    ));
                }
                (true, _) => {
                    return Err(format!(
                        "error: {name} has several definitions, none with this signature; \
                         rebind one with its own\n"
                    ));
                }
            };
            for i in gone {
                replaced[i] = true;
            }
        }
        let kept: Vec<Entry> = old
            .iter()
            .zip(&replaced)
            .filter(|(_, r)| !**r)
            .map(|(e, _)| e.clone())
            .collect();
        let entries = &mut self.session.entries;
        *entries = kept;
        entries.push(Entry {
            text: text.into(),
            names: names.clone(),
        });
        let fresh = entries.len() - 1;
        self.settle(fresh, old)?;
        let dependents = self.session.dependents(&names);
        Ok(EvalOutput::Rebound { names, dependents })
    }

    /// Adds the declarations of an input; their names must be new.
    fn define(&mut self, text: &str) -> Result<(), String> {
        let names = self.declared(text)?;
        let entries = self.session.entries.clone();
        if let Some(name) = names
            .iter()
            .find(|n| entries.iter().any(|e| self.redefines(text, e, n)))
        {
            return Err(format!(
                "error: {name} is already defined in this session; use :rebind\n"
            ));
        }
        let old = self.session.entries.clone();
        self.session.entries.push(Entry {
            text: text.into(),
            names,
        });
        self.settle(self.session.entries.len() - 1, old)
    }

    /// Checks the session with its new entries; with errors, it goes back
    /// to the old ones.
    fn settle(&mut self, fresh: usize, old: Vec<Entry>) -> Result<(), String> {
        self.fresh = Some(fresh);
        self.apply();
        let errors = self.errors();
        self.fresh = None;
        if !errors.is_empty() {
            self.session.entries = old;
            self.apply();
            return Err(errors);
        }
        Ok(())
    }

    /// Whether the definitions of `text` redefine `name` of an entry: it
    /// names something there that is not a function, or a function with
    /// the same signature. A function of another signature is an overload
    /// (§5.6.1).
    fn redefines(&self, text: &str, entry: &Entry, name: &str) -> bool {
        if !entry.names.iter().any(|n| n == name) {
            return false;
        }
        let db = &self.project.db;
        let items = |text: &str| {
            let alone = ModuleId::new(db, SESSION.into(), SourceFile::new(db, text.into()));
            item_tree(db, alone)
                .items
                .iter()
                .filter(|i| i.id.name(db).text(db) == name && *i.id.kind(db) != ItemKind::Slot)
                .map(|i| (*i.id.kind(db), i.signature.clone()))
                .collect::<Vec<_>>()
        };
        let (new, old) = (items(text), items(&entry.text));
        new.iter().any(|(kind, signature)| {
            old.iter().any(|(old_kind, old_signature)| {
                *kind != ItemKind::Function
                    || *old_kind != ItemKind::Function
                    || crag_hir::same_signature(signature, old_signature)
            })
        })
    }

    /// The names an input declares, or its syntax errors.
    fn declared(&mut self, text: &str) -> Result<Vec<String>, String> {
        let (_, errors) = crag_syntax::parse(text, &lex(text));
        if !errors.is_empty() {
            return Err(errors
                .iter()
                .map(|e| render_at("error", &e.message, "input", text, e.range.clone()))
                .collect());
        }
        // A module of its own, which no program has, says what it declares.
        let db = &self.project.db;
        let alone = ModuleId::new(db, SESSION.into(), SourceFile::new(db, text.into()));
        let mut names = Vec::new();
        for item in &item_tree(db, alone).items {
            let name = item.id.name(db).text(db);
            if *item.id.kind(db) != ItemKind::Slot && !names.contains(name) {
                names.push(name.clone());
            }
        }
        if names.iter().any(|n| n == INPUT) {
            return Err(format!("error: {INPUT} is the REPL's own name\n"));
        }
        Ok(names)
    }

    /// Runs an expression in the scratch image.
    fn evaluate(&mut self, text: &str) -> Result<EvalOutput, String> {
        self.input = Some(text.into());
        self.apply();
        let result = self.run_input();
        self.input = None;
        self.apply();
        result
    }

    fn run_input(&mut self) -> Result<EvalOutput, String> {
        let errors = self.errors();
        if !errors.is_empty() {
            return Err(errors);
        }
        let (db, program) = (&self.project.db, self.project.program);
        let item = item_tree(db, self.session.module)
            .items
            .iter()
            .map(|i| i.id)
            .find(|id| *id.kind(db) == ItemKind::Function && id.name(db).text(db) == INPUT)
            .expect("the input's function");
        let key = InstanceKey::body(db, Owner::Item(item));
        let ty = mir(db, program, key, Tier::Baseline)
            .as_ref()
            .expect("the input's function has a body")
            .result;
        self.shown_type = (ty != Ty::unit(db)).then(|| ty.display(db));
        // `()` shows nothing.
        let ran = match ty == Ty::unit(db) {
            true => self.scratch.execute(&self.project, key),
            false => self.scratch.show(&self.project, key, ty),
        };
        Ok(match ran.map_err(|e| format!("error: {e}\n"))? {
            RunResult::Finished(_) => EvalOutput::Value(None),
            RunResult::Shown(text) => EvalOutput::Value(Some(text)),
            RunResult::Trapped(trap) => EvalOutput::Stopped(self.scratch.report(self, &trap)),
            RunResult::Interrupted => EvalOutput::Stopped("interrupted\n".into()),
        })
    }

    /// Gives the session's module its text.
    fn apply(&mut self) {
        let text = self.session.layout(self.input.as_deref()).text;
        let file = self.session.module.file(&self.project.db);
        file.set_text(&mut self.project.db).to(text);
        self.project.read_resources();
    }

    /// The errors of the session's module, rendered.
    fn errors(&self) -> String {
        check(&self.project)
            .iter()
            .filter(|d| d.module == self.session.module)
            .map(|d| {
                let (file, source, start) = self.locate(d.module, d.range.start);
                let end = start + (d.range.end - d.range.start);
                render_at("error", &d.message, &file, source, start..end)
            })
            .collect()
    }

    /// The names an input may continue with: those of the session's scope,
    /// the prelude's and the imported ones among them, and keywords.
    pub fn completions(&self, prefix: &str) -> Vec<String> {
        let (db, program) = (&self.project.db, self.project.program);
        let mut out: BTreeSet<String> = module_scope(db, program, self.session.module)
            .names
            .keys()
            .map(|n| n.text(db).clone())
            .filter(|n| n.starts_with(prefix))
            .collect();
        for word in KEYWORDS {
            if word.starts_with(prefix) {
                out.insert(word.to_string());
            }
        }
        out.into_iter().collect()
    }
}

const KEYWORDS: [&str; 31] = [
    "let", "var", "ref", "ext", "embed", "type", "form", "fn", "test", "pub", "opaque", "distinct",
    "final", "is", "where", "on", "if", "else", "case", "pass", "for", "in", "return", "emit",
    "atomic", "lazy", "import", "as", "and", "or", "not",
];

impl Sources for Repl {
    /// A position in the session's module is shown in its input: the
    /// expression being run, the definition being added, or the definition
    /// by its first name.
    fn locate(&self, module: ModuleId, position: u32) -> (String, &str, u32) {
        if module != self.session.module {
            return self.project.locate(module, position);
        }
        let layout = self.session.layout(self.input.as_deref());
        if let (Some(start), Some(input)) = (layout.input, &self.input)
            && position >= start
        {
            return ("input".into(), input, position - start);
        }
        let i = layout
            .starts
            .iter()
            .rposition(|&s| s <= position)
            .unwrap_or(0);
        let Some(entry) = self.session.entries.get(i) else {
            return (SESSION.into(), "", 0);
        };
        let label = match (self.fresh, entry.names.first()) {
            (Some(fresh), _) if fresh == i => "input".to_string(),
            (_, Some(name)) => name.clone(),
            (_, None) => SESSION.into(),
        };
        let at = (position - layout.starts[i]).min(entry.text.len() as u32);
        (label, &entry.text, at)
    }
}
