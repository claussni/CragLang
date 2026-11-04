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

//! Receiving code (Implementation Plan §11.10.8, Specification §18.7): a
//! tree from elsewhere is checked again with the compiler's own front end
//! before anything runs it.
//!
//! The tree is written out as the source of a module of its own: every
//! function and type it names is imported under an alias of its own, its
//! helpers become private functions, and a function whose parameters are
//! the captures returns the root closure as an `Expr` of the type the
//! receiver expects. Names resolve against the receiver's packages,
//! inference checks the types, and the checks at a closure literal sent as
//! an `Expr` check that the code is `is Pure` and its captures `Solid`
//! and not `Secret`, helpers included. The receiver then builds the tree
//! of what it resolved and compares it with the sender's: references must
//! name the same functions and types as the policy asks, and everything
//! else must read back as sent.

use std::fmt::Write;

use crag_hir::ExprId;

use crag_backend::tree::{Name, TREE_VERSION, Value, decode_tree, encode_tree, expr_tree_value};
use crag_db::{RootDatabase, Setter};
use crag_hir::{
    Expr, ItemKind, ModuleId, Owner, Program, SourceFile, hir_body, item_tree, lower_body,
    module_scope, owners, parse,
};
use crag_types::ErrorKind;

use crag_hir::{lower_message as lower_error, name_message as name_error};

/// The path of the module a received tree is written to.
pub const RECEIVED: &str = "received$";

/// The function of that module that returns the received code, the
/// tree's number following it.
pub const ROOT: &str = "received";

/// Which references a receiver accepts (§18.7): the callee's body as the
/// sender's, the same major version of its package, or its module, name
/// and signature.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Accept {
    Exact,
    SameMajor,
    Signature,
}

/// Why received code was not accepted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Rejection {
    /// A reference the receiver cannot resolve, or resolves to code the
    /// policy does not accept.
    Unresolved(String),
    /// Code that does not check against the expected type, or a tree
    /// that is no well-formed code.
    IllTyped(String),
    /// Code that is not `is Pure`, or captures what is not `Solid` or
    /// holds a `Secret`.
    Impure(String),
}

/// Where a receiver checks the trees it receives: a program of the
/// receiver's modules and the module `RECEIVED`, whose source each tree
/// replaces.
///
/// Keeping one module frees what the database held for the trees before:
/// the queries of the module, and of the program as a whole, run again on
/// the new source, and the results for the items it no longer declares
/// are collected with those items once a few revisions passed without
/// reading them. A tree's items have names of their own, `received{n}`
/// and `h{n}_{i}` for the `n`th tree, so their instances, and with them
/// the code a receiver keeps by instance, never stand for another tree's.
pub struct Slot {
    base: Program,
    program: Program,
    module: ModuleId,
    file: SourceFile,
    trees: u64,
}

impl Slot {
    /// The slot of `base`'s modules and an empty received one.
    pub fn new(db: &mut RootDatabase, base: Program) -> Slot {
        let file = SourceFile::new(db, String::new());
        let module = ModuleId::new(db, RECEIVED.to_string(), file);
        let mut modules: Vec<ModuleId> = base
            .modules(db)
            .iter()
            .copied()
            .filter(|m| m.path(db) != RECEIVED)
            .collect();
        modules.push(module);
        let resources = base.resources(db).clone();
        let packages = base.packages(db).clone();
        let indices = base.type_indices(db).clone();
        let program = Program::new(db, modules, resources);
        program.set_packages(db).to(packages);
        if !indices.is_empty() {
            program.set_type_indices(db).to(indices);
        }
        Slot {
            base,
            program,
            module,
            file,
            trees: 0,
        }
    }

    /// The program the received code is checked in.
    pub fn program(&self) -> Program {
        self.program
    }
}

/// Received code that passed the check: the program with the module that
/// holds it, whose function `root` takes the captures and returns the
/// code.
#[derive(Clone, Debug)]
pub struct Checked {
    pub program: Program,
    pub module: ModuleId,
    /// The name of the function that returns the code.
    pub root: String,
    /// The root closure in the body of `root`.
    pub closure: ExprId,
    pub source: String,
    /// The callees accepted although their body hash differs from the
    /// sender's, each once as its module and name, which `run` signals as
    /// `HashMismatch` (§18.7).
    pub mismatched: Vec<(String, String)>,
}

/// Checks the bytes of a tree against `expected`, the function type the
/// receiver expects spelled out as a `TypeNode`, in the slot's program,
/// whose received module then holds the tree.
pub fn check_received(
    db: &mut RootDatabase,
    slot: &mut Slot,
    bytes: &[u8],
    expected: &Value,
    accept: Accept,
) -> Result<Checked, Rejection> {
    let malformed = |why: String| Rejection::IllTyped(format!("a malformed tree: {why}"));
    let sent = decode_tree(db, slot.base, bytes).map_err(malformed)?;
    let sent = normalize(sent);
    match field(&sent, "version") {
        Ok(Value::Int(TREE_VERSION)) => {}
        _ => {
            return Err(malformed(format!(
                "a tree of a version other than {TREE_VERSION}"
            )));
        }
    }
    let tree = slot.trees;
    let source = print(&sent, expected, tree).map_err(malformed)?;
    slot.trees += 1;
    slot.file.set_text(db).to(source.clone());
    let (received, module) = (slot.program, slot.module);
    let root = format!("{ROOT}{tree}");
    let db: &RootDatabase = db;
    errors(db, received, module)?;
    let item = item_tree(db, module)
        .items
        .iter()
        .find(|i| *i.id.kind(db) == ItemKind::Function && *i.id.name(db).text(db) == root)
        .map(|i| i.id)
        .ok_or_else(|| malformed("no root".into()))?;
    let owner = Owner::Item(item);
    let body = hir_body(db, received, owner);
    let closure = match body.root.map(|r| body.expr(r)) {
        Some(Expr::Block {
            stmts,
            tail: Some(t),
        }) if stmts.is_empty() => *t,
        _ => return Err(malformed("no root closure".into())),
    };
    let found = expr_tree_value(db, received, owner, closure, None).map_err(malformed)?;
    // Read back through the codec, so that both trees hold what bytes do.
    let found = encode_tree(db, received, &found).map_err(malformed)?;
    let found = normalize(decode_tree(db, received, &found).map_err(malformed)?);
    let mut mismatched = Vec::new();
    compare(&sent, &found, accept, &mut mismatched)?;
    Ok(Checked {
        program: received,
        module,
        root,
        closure,
        source,
        mismatched,
    })
}

/// The errors of the received module, the first one sorted by kind.
fn errors(db: &RootDatabase, program: Program, module: ModuleId) -> Result<(), Rejection> {
    if let Some(e) = parse(db, *module.file(db)).errors.first() {
        return Err(Rejection::IllTyped(e.message.clone()));
    }
    if let Some(e) = module_scope(db, program, module).errors.first() {
        return Err(Rejection::Unresolved(name_error(db, e)));
    }
    for owner in owners(db, module) {
        if let Some(e) = lower_body(db, program, owner).errors.first() {
            let (_, message) = lower_error(db, e);
            return Err(match e {
                crag_hir::LowerError::Unresolved { .. }
                | crag_hir::LowerError::UnknownType { .. } => Rejection::Unresolved(message),
                _ => Rejection::IllTyped(message),
            });
        }
    }
    let errors = crag_types::module_type_errors(db, program, module);
    // An impure body shows as an error of purity and, in what it gives,
    // of types: the first is the reason.
    let first_impure = errors.iter().find(|(_, e)| impure(db, &e.kind));
    if let Some((_, e)) = first_impure.or(errors.first()) {
        let message = e.kind.message(db);
        return Err(match &e.kind {
            k if impure(db, k) => Rejection::Impure(message),
            ErrorKind::PrivateTypeSent { .. } | ErrorKind::PrivateExpr { .. } => {
                Rejection::Unresolved(message)
            }
            _ => Rejection::IllTyped(message),
        });
    }
    if let Some(e) = crag_types::final_errors(db, program, module).first() {
        return Err(Rejection::IllTyped(e.error.kind.message(db)));
    }
    Ok(())
}

/// Whether an error says code is not `is Pure` or captures what may
/// not travel: a function where an `is Pure` one of the same parameters
/// and result is expected among them.
fn impure(db: &RootDatabase, kind: &ErrorKind) -> bool {
    match kind {
        ErrorKind::Effect { .. }
        | ErrorKind::PureCapture { .. }
        | ErrorKind::CellCapture { .. }
        | ErrorKind::SecretCapture { .. }
        | ErrorKind::ExprNotPure { .. }
        | ErrorKind::HandlerNotPure { .. } => true,
        ErrorKind::Mismatch { expected, found } => match (expected.as_fn(db), found.as_fn(db)) {
            (Some((pe, re, true)), Some((pf, rf, false))) => pe == pf && re == rf,
            _ => false,
        },
        _ => false,
    }
}

/// A block of no statements as the value it ends with, which it is: the
/// root closure of a named function holds its call alone, written as a
/// closure's block.
fn normalize(v: Value) -> Value {
    match v {
        Value::Record(name, fields) => {
            let fields: Vec<(Name, Value)> =
                fields.into_iter().map(|(n, v)| (n, normalize(v))).collect();
            if name == "Block"
                && matches!(fields.first(), Some((_, Value::List(s))) if s.is_empty())
                && !matches!(fields.get(1), Some((_, Value::Tag(t))) if t == "Empty")
            {
                if let Some((_, tail)) = fields.into_iter().nth(1) {
                    return tail;
                }
                unreachable!("a block has its tail");
            }
            Value::Record(name, fields)
        }
        Value::List(items) => Value::List(items.into_iter().map(normalize).collect()),
        v => v,
    }
}

/// Compares the sender's tree with the receiver's: references as the
/// policy asks, all else alike.
fn compare(
    sent: &Value,
    found: &Value,
    accept: Accept,
    mismatched: &mut Vec<(String, String)>,
) -> Result<(), Rejection> {
    let differs = || Rejection::IllTyped("the tree does not read back as it was sent".into());
    match (sent, found) {
        (Value::Record(a, fa), Value::Record(b, fb)) if a == b && fa.len() == fb.len() => {
            if a == "FnRef" || a == "TypeRef" {
                return reference(a, sent, found, accept, mismatched);
            }
            for ((na, va), (nb, vb)) in fa.iter().zip(fb) {
                if na != nb {
                    return Err(differs());
                }
                compare(va, vb, accept, mismatched)?;
            }
            Ok(())
        }
        (Value::List(a), Value::List(b)) if a.len() == b.len() => {
            for (va, vb) in a.iter().zip(b) {
                compare(va, vb, accept, mismatched)?;
            }
            Ok(())
        }
        (a, b) if a == b => Ok(()),
        _ => Err(differs()),
    }
}

/// A function's or a type's reference, which must name what the sender
/// named in the same module, and as much more as the policy asks.
fn reference(
    kind: &str,
    sent: &Value,
    found: &Value,
    accept: Accept,
    mismatched: &mut Vec<(String, String)>,
) -> Result<(), Rejection> {
    let get = |v: &Value, name: &str| field(v, name).cloned().unwrap_or(Value::List(Vec::new()));
    let same = |name: &str| get(sent, name) == get(found, name);
    let shown = match (get(sent, "module"), get(sent, "name")) {
        (Value::Str(m), Value::Str(n)) => format!("`{m}.{n}`"),
        _ => "a reference".into(),
    };
    let unresolved = |why: &str| Err(Rejection::Unresolved(format!("{shown} {why}")));
    if !same("module") || !same("name") {
        return unresolved("resolves to another declaration");
    }
    let package = same("package") && same("major");
    let (structure, hash) = match kind {
        "FnRef" => ("signature", "body"),
        _ => ("args", "hash"),
    };
    // Type arguments are compared alike under every policy, and a
    // signature under the policy that names it, by the same rules.
    let shape = compare(
        &get(sent, structure),
        &get(found, structure),
        accept,
        mismatched,
    );
    match accept {
        Accept::Exact if !package || !same(hash) => {
            return unresolved("differs from the sender's, which `Exact` does not accept");
        }
        Accept::SameMajor if !package => {
            return unresolved("is of another major version of its package");
        }
        Accept::Signature | Accept::Exact => {
            if shape.is_err() {
                return unresolved("has another signature than the sender's");
            }
        }
        Accept::SameMajor if kind == "TypeRef" && shape.is_err() => {
            return unresolved("has other type arguments than the sender's");
        }
        Accept::SameMajor => {}
    }
    if kind == "FnRef"
        && !same(hash)
        && let (Value::Str(m), Value::Str(n)) = (get(sent, "module"), get(sent, "name"))
        && !mismatched.iter().any(|(a, b)| *a == m && *b == n)
    {
        mismatched.push((m, n));
    }
    Ok(())
}

fn field<'v>(v: &'v Value, name: &str) -> Result<&'v Value, String> {
    match v {
        Value::Record(r, fields) => fields
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, v)| v)
            .ok_or_else(|| format!("{r} has no field {name}")),
        _ => Err(format!("{v:?} has no field {name}")),
    }
}

/// The source of the module that holds a tree, the `n`th it received.
fn print(tree: &Value, expected: &Value, n: u64) -> Result<String, String> {
    let mut p = Printer {
        imports: Vec::new(),
        helpers: list(field(tree, "helpers")?)?.len(),
        tree: n,
    };
    let mut items = String::new();
    for (i, helper) in list(field(tree, "helpers")?)?.iter().enumerate() {
        let params = list(field(helper, "params")?)?;
        let count = int(field(helper, "typeParams")?)?;
        if !(0..=64).contains(&count) {
            return Err("a helper with too many type parameters".into());
        }
        let _ = write!(items, "fn h{n}_{i}");
        if count > 0 {
            let names: Vec<String> = (0..count).map(|k| format!("P{k}")).collect();
            let _ = write!(items, "[{}]", names.join(", "));
        }
        let params = p.fn_params(params)?;
        let result = p.ty(field(helper, "result")?)?;
        let body = p.block_body(field(helper, "body")?, 1)?;
        let _ = write!(items, "({params}) -> {result} {body}\n\n");
    }
    let captures = list(field(tree, "captures")?)?
        .iter()
        .enumerate()
        .map(|(i, t)| Ok(format!("c{i}: {}", p.ty(t)?)))
        .collect::<Result<Vec<_>, String>>()?;
    let expr = p.type_alias("std.transport", "Expr")?;
    let expected = p.ty(expected)?;
    let root = p.closure(field(tree, "root")?, 1)?;
    let _ = write!(
        items,
        "fn {ROOT}{n}({}) -> {expr}[{expected}] {{\n  {root}\n}}\n",
        captures.join(", ")
    );
    let mut out = String::new();
    let mut modules: Vec<&str> = p.imports.iter().map(|i| i.0.as_str()).collect();
    modules.dedup();
    modules.sort();
    modules.dedup();
    for module in modules {
        let names: Vec<String> = p
            .imports
            .iter()
            .filter(|i| i.0 == module)
            .map(|i| format!("{} as {}", i.1, i.2))
            .collect();
        let _ = writeln!(out, "import {module}.{{{}}}", names.join(", "));
    }
    out.push('\n');
    out.push_str(&items);
    Ok(out)
}

fn list(v: &Value) -> Result<&[Value], String> {
    match v {
        Value::List(items) => Ok(items),
        _ => Err(format!("{v:?} is no list")),
    }
}

fn int(v: &Value) -> Result<i64, String> {
    match v {
        Value::Int(n) => Ok(*n),
        _ => Err(format!("{v:?} is no number")),
    }
}

fn string(v: &Value) -> Result<&str, String> {
    match v {
        Value::Str(s) => Ok(s),
        _ => Err(format!("{v:?} is no string")),
    }
}

fn boolean(v: &Value) -> Result<bool, String> {
    match v {
        Value::Bool(b) => Ok(*b),
        Value::Tag(t) if t == "True" => Ok(true),
        Value::Tag(t) if t == "False" => Ok(false),
        _ => Err(format!("{v:?} is no Bool")),
    }
}

/// An optional field's value.
fn option(v: &Value) -> Option<&Value> {
    match v {
        Value::Tag(t) if t == "Empty" => None,
        v => Some(v),
    }
}

/// The name of a record's type or a tag.
fn kind(v: &Value) -> &str {
    match v {
        Value::Record(name, _) | Value::Tag(name) => name,
        _ => "",
    }
}

/// A name the tree gives, which must be a plain identifier: the source
/// is never anything but code of the tree's own shape.
fn ident(name: &str) -> Result<&str, String> {
    let mut chars = name.chars();
    let first = chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_');
    if first && chars.all(|c| c.is_ascii_alphanumeric() || c == '_') {
        Ok(name)
    } else {
        Err(format!("`{name}` is no name"))
    }
}

fn module_path(path: &str) -> Result<&str, String> {
    for segment in path.split('.') {
        ident(segment)?;
    }
    Ok(path)
}

fn index(v: &Value) -> Result<usize, String> {
    usize::try_from(int(v)?).map_err(|_| "a negative index".to_string())
}

/// Text as it is written between the quotes of a string literal.
fn escaped(text: &str) -> String {
    let mut out = String::new();
    for c in text.chars() {
        match c {
            '"' | '\\' | '\'' => {
                out.push('\\');
                out.push(c);
            }
            '{' => out.push_str("{{"),
            '}' => out.push_str("}}"),
            ' '..='~' => out.push(c),
            c => {
                let _ = write!(out, "\\u{{{:x}}}", c as u32);
            }
        }
    }
    out
}

struct Printer {
    /// The functions and types named, by module and name, and the alias
    /// each is imported as.
    imports: Vec<(String, String, String)>,
    helpers: usize,
    /// The tree's number, which its helpers' names carry.
    tree: u64,
}

impl Printer {
    fn alias(&mut self, module: &str, name: &str, prefix: char) -> Result<String, String> {
        module_path(module)?;
        ident(name)?;
        if let Some(i) = self
            .imports
            .iter()
            .find(|i| i.0 == module && i.1 == name && i.2.starts_with(prefix))
        {
            return Ok(i.2.clone());
        }
        let alias = format!("{prefix}{}", self.imports.len());
        self.imports
            .push((module.to_string(), name.to_string(), alias.clone()));
        Ok(alias)
    }

    fn type_alias(&mut self, module: &str, name: &str) -> Result<String, String> {
        self.alias(module, name, 'N')
    }

    // Types.

    fn ty(&mut self, v: &Value) -> Result<String, String> {
        Ok(match kind(v) {
            "Named" => self.named(v)?,
            "RecordType" => {
                let mut fields = Vec::new();
                for f in list(field(v, "fields")?)? {
                    let name = ident(string(field(f, "name")?)?)?;
                    fields.push(format!("{name}: {}", self.ty(field(f, "ty")?)?));
                }
                if boolean(field(v, "open")?)? {
                    fields.push("..".into());
                }
                format!("({})", fields.join(", "))
            }
            "FnType" => {
                let params = list(field(v, "params")?)?
                    .iter()
                    .map(|t| self.ty(t))
                    .collect::<Result<Vec<_>, _>>()?;
                let result = self.ty(field(v, "result")?)?;
                let pure = match boolean(field(v, "pure")?)? {
                    true => " is Pure",
                    false => "",
                };
                format!("(({}) -> {result}{pure})", params.join(", "))
            }
            "UnionType" => {
                let members = list(field(v, "members")?)?
                    .iter()
                    .map(|t| {
                        let t = self.ty(t)?;
                        Ok(match t.contains(" | ") && !t.starts_with('(') {
                            true => format!("({t})"),
                            false => t,
                        })
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                if members.len() < 2 {
                    return Err("a union of fewer than two members".into());
                }
                members.join(" | ")
            }
            "UnitType" => "()".into(),
            "TypeParam" => format!("P{}", index(field(v, "index")?)?),
            _ => return Err(format!("{v:?} is no type")),
        })
    }

    /// A named type by its alias, with its arguments.
    fn named(&mut self, v: &Value) -> Result<String, String> {
        if kind(v) != "Named" {
            return Err("a type here must be a named one".into());
        }
        let r = field(v, "ty")?;
        let module = string(field(r, "module")?)?;
        let name = string(field(r, "name")?)?;
        let alias = self.type_alias(module, name)?;
        let args = list(field(r, "args")?)?;
        if args.is_empty() {
            return Ok(alias);
        }
        let args = args
            .iter()
            .map(|a| match kind(a) {
                "Scale" => Ok(index(field(a, "digits")?)?.to_string()),
                _ => self.ty(a),
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(format!("{alias}[{}]", args.join(", ")))
    }

    // Functions.

    fn fn_params(&mut self, params: &[Value]) -> Result<String, String> {
        let mut out = Vec::new();
        for p in params {
            let local = index(field(p, "local")?)?;
            let ty = self.ty(field(p, "ty")?)?;
            let mut param = format!("l{local}: {ty}");
            if let Some(d) = option(field(p, "default")?) {
                let _ = write!(param, " = {}", self.expr(d, 2)?);
            }
            out.push(param);
        }
        Ok(out.join(", "))
    }

    fn closure(&mut self, v: &Value, depth: usize) -> Result<String, String> {
        if kind(v) != "Closure" {
            return Err("a closure that is none".into());
        }
        let mut params = Vec::new();
        for p in list(field(v, "params")?)? {
            let pat = self.pat(field(p, "pat")?)?;
            params.push(match option(field(p, "ty")?) {
                Some(t) => format!("{pat}: {}", self.ty(t)?),
                None => pat,
            });
        }
        let head = match params.is_empty() {
            true => "{ ->".to_string(),
            false => format!("{{ {} ->", params.join(", ")),
        };
        let body = self.statements(field(v, "body")?, depth + 1)?;
        Ok(format!("{head}\n{body}{}}}", pad(depth)))
    }

    /// A node as the block of a function, an `if` or a loop.
    fn block_body(&mut self, v: &Value, depth: usize) -> Result<String, String> {
        Ok(format!(
            "{{\n{}{}}}",
            self.statements(v, depth)?,
            pad(depth - 1)
        ))
    }

    /// The lines of a block, or of a value that stands for one.
    fn statements(&mut self, v: &Value, depth: usize) -> Result<String, String> {
        let mut out = String::new();
        if kind(v) == "Block" {
            for s in list(field(v, "stmts")?)? {
                let _ = writeln!(out, "{}{}", pad(depth), self.stmt(s, depth)?);
            }
            if let Some(tail) = option(field(v, "tail")?) {
                let _ = writeln!(out, "{}{}", pad(depth), self.expr(tail, depth)?);
            }
        } else {
            let _ = writeln!(out, "{}{}", pad(depth), self.expr(v, depth)?);
        }
        Ok(out)
    }

    fn stmt(&mut self, v: &Value, depth: usize) -> Result<String, String> {
        let typed = |this: &mut Self, v: &Value| -> Result<String, String> {
            Ok(match option(field(v, "ty")?) {
                Some(t) => format!(": {}", this.ty(t)?),
                None => String::new(),
            })
        };
        Ok(match kind(v) {
            "ExprStmt" => self.expr(field(v, "value")?, depth)?,
            "Let" => {
                let pat = self.pat(field(v, "pat")?)?;
                let ty = typed(self, v)?;
                format!("let {pat}{ty} = {}", self.expr(field(v, "value")?, depth)?)
            }
            "LetElse" => {
                let pat = self.pat(field(v, "pat")?)?;
                let ty = typed(self, v)?;
                let value = self.expr(field(v, "value")?, depth)?;
                let head = match option(field(v, "rest")?) {
                    Some(rest) => format!("{{ {} ->", self.pat(rest)?),
                    None => "{".into(),
                };
                let body = self.statements(field(v, "otherwise")?, depth + 1)?;
                format!(
                    "let {pat}{ty} = {value} else {head}\n{body}{}}}",
                    pad(depth)
                )
            }
            "Var" => {
                let local = index(field(v, "local")?)?;
                let ty = typed(self, v)?;
                format!(
                    "var l{local}{ty} = {}",
                    self.expr(field(v, "value")?, depth)?
                )
            }
            "Assign" => {
                let local = index(field(v, "local")?)?;
                format!("l{local} = {}", self.expr(field(v, "value")?, depth)?)
            }
            "For" => {
                let pat = self.pat(field(v, "pat")?)?;
                let iterable = self.expr(field(v, "iterable")?, depth)?;
                let body = self.block_body(field(v, "body")?, depth + 1)?;
                format!("for {pat} in ({iterable}) {body}")
            }
            "Return" => match option(field(v, "value")?) {
                Some(e) => format!("return {}", self.expr(e, depth)?),
                None => "return".into(),
            },
            "LocalFn" => {
                let local = index(field(v, "local")?)?;
                let params = self.fn_params(list(field(v, "params")?)?)?;
                let result = match option(field(v, "result")?) {
                    Some(t) => format!(" -> {}", self.ty(t)?),
                    None => String::new(),
                };
                let pure = boolean(field(v, "pure")?)?;
                if pure && result.is_empty() {
                    return Err("an `is Pure` local function without a result type".into());
                }
                let pure = if pure { " is Pure" } else { "" };
                let body = self.block_body(field(v, "body")?, depth + 1)?;
                format!("fn l{local}({params}){result}{pure} {body}")
            }
            _ => return Err(format!("{v:?} is no statement")),
        })
    }

    // Expressions, each compound one in parentheses.

    fn exprs(&mut self, v: &Value, depth: usize) -> Result<Vec<String>, String> {
        list(v)?.iter().map(|e| self.expr(e, depth)).collect()
    }

    /// An expression where a callee, a receiver or an operand goes: a
    /// name as it is, anything else in parentheses.
    fn operand(&mut self, v: &Value, depth: usize) -> Result<String, String> {
        let e = self.expr(v, depth)?;
        Ok(match kind(v) {
            "CaptureRef" | "LocalRef" | "HelperRef" | "Function" => e,
            "TypeName" if !e.contains('[') => e,
            _ => format!("({e})"),
        })
    }

    fn expr(&mut self, v: &Value, depth: usize) -> Result<String, String> {
        Ok(match kind(v) {
            "IntLit" => {
                let digits = string(field(v, "digits")?)?;
                let unsigned = digits.strip_prefix('-').unwrap_or(digits);
                if unsigned.is_empty() || !unsigned.chars().all(|c| c.is_ascii_digit()) {
                    return Err(format!("`{digits}` is no number"));
                }
                match digits.starts_with('-') {
                    true => format!("({digits})"),
                    false => digits.to_string(),
                }
            }
            "FloatLit" => {
                let digits = string(field(v, "digits")?)?;
                let unsigned = digits.strip_prefix('-').unwrap_or(digits);
                let number = unsigned.starts_with(|c: char| c.is_ascii_digit())
                    && unsigned
                        .chars()
                        .all(|c| c.is_ascii_digit() || matches!(c, '.' | 'e' | 'E' | '+' | '-'));
                if !number {
                    return Err(format!("`{digits}` is no number"));
                }
                match digits.starts_with('-') {
                    true => format!("({digits})"),
                    false => digits.to_string(),
                }
            }
            "StrLit" => format!("\"{}\"", escaped(string(field(v, "value")?)?)),
            "BytesLit" => {
                let Value::Bytes(bytes) = field(v, "value")? else {
                    return Err("bytes that are none".into());
                };
                let mut out = String::from("b\"");
                for b in bytes {
                    let _ = write!(out, "\\x{b:02x}");
                }
                out.push('"');
                out
            }
            "CodePointLit" => match field(v, "value")? {
                Value::CodePoint(c) => format!("'\\u{{{:x}}}'", *c as u32),
                _ => return Err("a code point that is none".into()),
            },
            "Text" => {
                let mut out = String::from("\"");
                for part in list(field(v, "parts")?)? {
                    match part {
                        Value::Str(s) => out.push_str(&escaped(s)),
                        node => {
                            let _ = write!(out, "{{{}}}", self.expr(node, depth)?);
                        }
                    }
                }
                out.push('"');
                out
            }
            "CaptureRef" => format!("c{}", index(field(v, "index")?)?),
            "LocalRef" => format!("l{}", index(field(v, "index")?)?),
            "HelperRef" => {
                let i = index(field(v, "index")?)?;
                if i >= self.helpers {
                    return Err("a helper the tree does not bundle".into());
                }
                format!("h{}_{i}", self.tree)
            }
            "Function" => {
                let r = field(v, "target")?;
                let module = string(field(r, "module")?)?;
                let name = string(field(r, "name")?)?;
                self.alias(module, name, 'f')?
            }
            "TypeName" => self.named(field(v, "ty")?)?,
            "Call" => {
                let callee = self.operand(field(v, "callee")?, depth)?;
                let targs = list(field(v, "typeArgs")?)?
                    .iter()
                    .map(|t| self.ty(t))
                    .collect::<Result<Vec<_>, _>>()?;
                let mut args = self.exprs(field(v, "args")?, depth)?;
                args.extend(self.fields(field(v, "fields")?, depth)?);
                let targs = match targs.is_empty() {
                    true => String::new(),
                    false => format!("[{}]", targs.join(", ")),
                };
                format!("{callee}{targs}({})", args.join(", "))
            }
            "Field" => {
                let receiver = self.operand(field(v, "receiver")?, depth)?;
                let name = ident(string(field(v, "name")?)?)?;
                let dot = if boolean(field(v, "optional")?)? {
                    "?."
                } else {
                    "."
                };
                format!("{receiver}{dot}{name}")
            }
            "Index" => {
                let base = self.operand(field(v, "base")?, depth)?;
                format!(
                    "{base}[{}]",
                    self.exprs(field(v, "args")?, depth)?.join(", ")
                )
            }
            "And" | "Or" => {
                let left = self.operand(field(v, "left")?, depth)?;
                let right = self.operand(field(v, "right")?, depth)?;
                let op = if kind(v) == "And" { "and" } else { "or" };
                format!("{left} {op} {right}")
            }
            "Not" => format!("not {}", self.operand(field(v, "value")?, depth)?),
            "RangeNode" => {
                let start = self.operand(field(v, "start")?, depth)?;
                match option(field(v, "end")?) {
                    Some(end) => format!("{start}..{}", self.operand(end, depth)?),
                    None => format!("{start}.."),
                }
            }
            "Is" => {
                let value = self.operand(field(v, "value")?, depth)?;
                format!("{value} is {}", self.ty(field(v, "ty")?)?)
            }
            "RecordNode" => format!("({})", self.fields(field(v, "fields")?, depth)?.join(", ")),
            "ListNode" => format!("[{}]", self.exprs(field(v, "items")?, depth)?.join(", ")),
            "MapNode" => {
                let mut entries = Vec::new();
                for e in list(field(v, "entries")?)? {
                    let key = self.expr(field(e, "key")?, depth)?;
                    let value = self.expr(field(e, "value")?, depth)?;
                    entries.push(format!("{key}: {value}"));
                }
                match entries.is_empty() {
                    true => "[:]".into(),
                    false => format!("[{}]", entries.join(", ")),
                }
            }
            "GridNode" => {
                let rows = list(field(v, "rows")?)?
                    .iter()
                    .map(|r| Ok(self.exprs(r, depth)?.join(", ")))
                    .collect::<Result<Vec<_>, String>>()?;
                if rows.len() < 2 {
                    return Err("a grid of fewer than two rows".into());
                }
                format!("[{}]", rows.join("; "))
            }
            "Block" => self.block_body(v, depth + 1)?,
            "If" => {
                let condition = self.expr(field(v, "condition")?, depth)?;
                let then = self.block_body(field(v, "then")?, depth + 1)?;
                match option(field(v, "otherwise")?) {
                    Some(o) => {
                        let otherwise = self.block_body(o, depth + 1)?;
                        format!("if {condition} {then} else {otherwise}")
                    }
                    None => format!("if {condition} {then}"),
                }
            }
            "Case" => {
                let subject = self.operand(field(v, "subject")?, depth)?;
                let mut out = format!("case {subject} {{\n");
                for arm in list(field(v, "arms")?)? {
                    let pat = self.pat(field(arm, "pat")?)?;
                    let guard = match option(field(arm, "guard")?) {
                        Some(g) => format!(" where {}", self.expr(g, depth + 1)?),
                        None => String::new(),
                    };
                    let body = self.expr(field(arm, "body")?, depth + 1)?;
                    let _ = writeln!(out, "{}{pat}{guard} -> {body}", pad(depth + 1));
                }
                let _ = write!(out, "{}}}", pad(depth));
                out
            }
            "Pass" => "pass".into(),
            "LazyNode" => format!("lazy {}", self.operand(field(v, "value")?, depth)?),
            "Closure" => self.closure(v, depth)?,
            _ => return Err(format!("{v:?} is no expression")),
        })
    }

    /// Named arguments and spreads, or the fields of a record.
    fn fields(&mut self, v: &Value, depth: usize) -> Result<Vec<String>, String> {
        let mut out = Vec::new();
        for f in list(v)? {
            out.push(match kind(f) {
                "FieldArg" => {
                    let path = list(field(f, "path")?)?
                        .iter()
                        .map(|n| Ok(ident(string(n)?)?.to_string()))
                        .collect::<Result<Vec<_>, String>>()?;
                    if path.is_empty() {
                        return Err("a field without a name".into());
                    }
                    format!(
                        "{}: {}",
                        path.join("."),
                        self.expr(field(f, "value")?, depth)?
                    )
                }
                "Spread" => format!("..{}", self.operand(field(f, "value")?, depth)?),
                _ => return Err(format!("{f:?} is no field")),
            });
        }
        Ok(out)
    }

    // Patterns.

    fn pat(&mut self, v: &Value) -> Result<String, String> {
        Ok(match kind(v) {
            "Wildcard" => "_".into(),
            "Bind" => {
                let local = index(field(v, "local")?)?;
                match option(field(v, "sub")?) {
                    Some(sub) => format!("l{local}: {}", self.pat(sub)?),
                    None => format!("l{local}"),
                }
            }
            "TypePat" => self.named(field(v, "ty")?)?,
            "RecordPat" => {
                let ty = match option(field(v, "ty")?) {
                    Some(t) => self.named(t)?,
                    None => String::new(),
                };
                let mut fields = Vec::new();
                for f in list(field(v, "fields")?)? {
                    let pat = self.pat(field(f, "pat")?)?;
                    fields.push(match option(field(f, "name")?) {
                        Some(n) => format!("{}: {pat}", ident(string(n)?)?),
                        None => pat,
                    });
                }
                format!("{ty}({})", fields.join(", "))
            }
            "ListPat" => {
                let mut items = Vec::new();
                for p in list(field(v, "before")?)? {
                    items.push(self.pat(p)?);
                }
                if let Some(rest) = option(field(v, "rest")?) {
                    items.push(match option(field(rest, "local")?) {
                        Some(l) => format!("..l{}", index(l)?),
                        None => "..".into(),
                    });
                }
                for p in list(field(v, "after")?)? {
                    items.push(self.pat(p)?);
                }
                format!("[{}]", items.join(", "))
            }
            "LitPat" => self.lit_pat(v)?,
            "RangePat" => format!(
                "{}..{}",
                self.lit_pat(field(v, "start")?)?,
                self.lit_pat(field(v, "end")?)?
            ),
            "OrPat" => {
                let alternatives = list(field(v, "alternatives")?)?
                    .iter()
                    .map(|p| self.pat(p))
                    .collect::<Result<Vec<_>, _>>()?;
                if alternatives.len() < 2 {
                    return Err("an or-pattern of fewer than two alternatives".into());
                }
                alternatives.join(" | ")
            }
            _ => return Err(format!("{v:?} is no pattern")),
        })
    }

    fn lit_pat(&mut self, v: &Value) -> Result<String, String> {
        let lit = field(v, "lit")?;
        let negative = boolean(field(v, "negative")?)?;
        let text = match kind(lit) {
            "IntLit" | "FloatLit" => {
                let digits = string(field(lit, "digits")?)?;
                if digits.starts_with('-') {
                    return Err("a pattern's digits with a sign".into());
                }
                self.expr(lit, 0)?
            }
            "StrLit" | "BytesLit" | "CodePointLit" if !negative => self.expr(lit, 0)?,
            _ => return Err(format!("{lit:?} is no literal pattern")),
        };
        Ok(match negative {
            true => format!("-{text}"),
            false => text,
        })
    }
}

fn pad(depth: usize) -> String {
    "  ".repeat(depth)
}
