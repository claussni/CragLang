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

    fn defines(&self, name: &str) -> bool {
        self.entries
            .iter()
            .any(|e| e.names.iter().any(|n| n == name))
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
        Some(Fn | Type | Let | Import | Pub | Form | Embed | Test | Distinct | Opaque)
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
        }
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
            _ => Err(format!(
                "error: there is no command :{name}; :help lists them\n"
            )),
        }
    }

    /// Replaces the definitions of the names a definition declares. Each
    /// must be defined in the session.
    pub fn rebind(&mut self, text: &str) -> Result<EvalOutput, String> {
        let names = self.declared(text)?;
        if names.is_empty() {
            return Err("error: :rebind takes a definition\n".into());
        }
        if let Some(name) = names.iter().find(|n| !self.session.defines(n)) {
            return Err(format!(
                "error: {name} is not defined in this session; define it without :rebind\n"
            ));
        }
        let old = self.session.entries.clone();
        let entries = &mut self.session.entries;
        entries.retain(|e| !e.names.iter().any(|n| names.contains(n)));
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
        if let Some(name) = names.iter().find(|n| self.session.defines(n)) {
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

const KEYWORDS: [&str; 30] = [
    "let", "var", "ref", "ext", "embed", "type", "form", "fn", "test", "pub", "opaque", "distinct",
    "is", "where", "on", "if", "else", "case", "pass", "for", "in", "return", "emit", "atomic",
    "lazy", "import", "as", "and", "or", "not",
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
