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

//! Code trees (Implementation Plan §11.10.11): the body of an `Expr` as a
//! value of `std.transport.Tree`, written in the Solid codec.
//!
//! A tree is resolved HIR without inferred types. Locals, the root's
//! parameters first, are numbered in order of introduction in a pre-order
//! walk, and captures apart. A call names its one callee: a `pub` function
//! by a `FnRef`, any other function by its place among the helpers, which
//! the tree bundles in order of first reference. Written types travel
//! spelled out, a named type by a `TypeRef` with its canonical hash.
//!
//! The tree is built as a `Value` and encoded by walking the shapes of
//! `Tree` as the runtime's codec walks a value's words, so the bytes are
//! the codec's and `e.tree` decodes them with it.

use std::borrow::Cow;

use crag_abi::wire;
use crag_abi::{Shape, Shapes, narrow};
use crag_db::Db;
use crag_hir::{
    BindingId, BindingKind, Body, Expr, ExprId, FieldArg, ItemId, ItemKind, Literal, Owner, Pat,
    PatId, PatLiteral, Program, Resolution, Stmt, StrPart, TypeRefId, hir_body, item_tree,
    type_identity,
};
use crag_types::{
    Builtin, Callee, InferenceResult, Ty, TyKind, body_types, function_effects, is_public,
    module_values, result_type, signature, subst, type_hash, value_type,
};

use crate::shape::shapes;

/// The version of the tree format, which a change to the types of
/// `std.transport` raises.
pub const TREE_VERSION: i64 = 1;

/// A value of one of the types of `std.transport`, as the encoder walks
/// it: a record by its type's name and its fields by name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Int(i64),
    Str(String),
    Bytes(Vec<u8>),
    CodePoint(char),
    Bool(bool),
    List(Vec<Value>),
    Record(Name, Vec<(Name, Value)>),
    Tag(Name),
}

/// The name of a type or a field: the builder's own, or one a decoded
/// tree carries.
pub type Name = Cow<'static, str>;

fn record(name: &'static str, fields: Vec<(&'static str, Value)>) -> Value {
    Value::Record(
        name.into(),
        fields.into_iter().map(|(n, v)| (n.into(), v)).collect(),
    )
}

fn tag(name: &'static str) -> Value {
    Value::Tag(name.into())
}

fn int(n: impl TryInto<i64>) -> Value {
    Value::Int(n.try_into().unwrap_or(i64::MAX))
}

fn option(v: Option<Value>) -> Value {
    v.unwrap_or(tag("Empty"))
}

fn text(t: &str) -> Value {
    Value::Str(t.to_string())
}

/// What the tree cannot hold yet, or holds wrong; the checks at the
/// literal report what is the program's fault.
pub type Untreeable = String;

/// The type of `std.transport`'s declaration `name`, if the program has
/// it.
pub fn transport_type<'db>(db: &'db dyn Db, program: Program, name: &str) -> Option<Ty<'db>> {
    let module = program
        .modules(db)
        .iter()
        .find(|m| m.path(db) == "std.transport")?;
    let item = item_tree(db, *module)
        .items
        .iter()
        .find(|i| *i.id.kind(db) == ItemKind::Type && i.id.name(db).text(db) == name)?
        .id;
    let identity = type_identity(db, program, item);
    Some(Ty::new(db, TyKind::Named(identity, Vec::new())))
}

/// The bytes of a tree, of the shape of `Tree`.
pub fn encode_tree(db: &dyn Db, program: Program, tree: &Value) -> Result<Vec<u8>, Untreeable> {
    encode_transport(db, program, "Tree", tree)
}

/// The bytes of a value of the type `name` of `std.transport`, such as a
/// `TypeNode`.
pub fn encode_transport(
    db: &dyn Db,
    program: Program,
    name: &str,
    value: &Value,
) -> Result<Vec<u8>, Untreeable> {
    let ty = transport_type(db, program, name).ok_or("a program without std.transport")?;
    let (shapes, root) = shapes(db, program, ty);
    let mut out = Vec::new();
    encode(value, &shapes, root, &mut out)?;
    Ok(out)
}

/// Writes the value as the codec writes a value of the shape (see
/// `crag_runtime::codec`).
fn encode(v: &Value, shapes: &Shapes, shape: u32, out: &mut Vec<u8>) -> Result<(), Untreeable> {
    if let Some(stored) = shapes.plain(shape) {
        let Shape::Stored {
            form, size, slots, ..
        } = &shapes.shapes[stored as usize]
        else {
            return Err(format!("shape {stored} is no storage form"));
        };
        let register = words(v, shapes, *form)?;
        let at = out.len();
        out.resize(at + *size as usize, 0);
        narrow(slots, &register, &mut out[at..]);
        return Ok(());
    }
    match (&shapes.shapes[shape as usize], v) {
        (Shape::Unit | Shape::Tag(_), _) => {}
        (Shape::Number(_), Value::Int(n)) => out.extend(n.to_le_bytes()),
        (Shape::Number(_), Value::CodePoint(c)) => out.extend(u64::from(*c).to_le_bytes()),
        (Shape::Union { members, .. } | Shape::Variant { members, .. }, _) => {
            let at = member(v, shapes, members)?;
            out.extend((at as u32).to_le_bytes());
            encode(v, shapes, members[at].1, out)?;
        }
        (Shape::Record { name, fields }, Value::Record(..)) => {
            if name.is_some() {
                let identity = shapes.identity(shape).ok_or("a record without identity")?;
                out.extend(identity);
            }
            for f in fields {
                let shape = match &shapes.shapes[f.shape as usize] {
                    Shape::Stored { form, .. } => *form,
                    _ => f.shape,
                };
                encode(field(v, &f.name)?, shapes, shape, out)?;
            }
        }
        (Shape::Inline { fields, .. }, Value::Record(..)) => {
            for f in fields {
                encode(field(v, &f.name)?, shapes, f.shape, out)?;
            }
        }
        (&Shape::List(element), Value::List(items)) => {
            let element = match &shapes.shapes[element as usize] {
                Shape::Stored { form, .. } => *form,
                _ => element,
            };
            out.extend((items.len() as u64).to_le_bytes());
            for item in items {
                encode(item, shapes, element, out)?;
            }
        }
        (Shape::Str, Value::Str(s)) => {
            out.extend((s.len() as u64).to_le_bytes());
            out.extend(s.as_bytes());
        }
        (Shape::Bytes, Value::Bytes(b)) => {
            out.extend((b.len() as u64).to_le_bytes());
            out.extend(b);
        }
        (s, v) => return Err(format!("{v:?} as {s:?}")),
    }
    Ok(())
}

/// The register form of a Plain value of the shape.
fn words(v: &Value, shapes: &Shapes, shape: u32) -> Result<Vec<u64>, Untreeable> {
    Ok(match (&shapes.shapes[shape as usize], v) {
        (Shape::Unit | Shape::Tag(_), _) => Vec::new(),
        (Shape::Number(_), Value::Int(n)) => vec![*n as u64],
        (Shape::Number(_), Value::CodePoint(c)) => vec![u64::from(*c)],
        (Shape::Union { members, words: n } | Shape::Variant { members, words: n }, _) => {
            let at = member(v, shapes, members)?;
            let mut out = vec![u64::from(members[at].0)];
            out.extend(words(v, shapes, members[at].1)?);
            out.resize((*n as usize).max(1), 0);
            out
        }
        (
            Shape::Inline {
                fields, words: n, ..
            },
            Value::Record(..),
        ) => {
            let mut out = vec![0; *n as usize];
            for f in fields {
                let value = words(field(v, &f.name)?, shapes, f.shape)?;
                let at = f.offset as usize;
                out[at..at + value.len()].copy_from_slice(&value);
            }
            out
        }
        (s, v) => return Err(format!("{v:?} in the register form {s:?}")),
    })
}

/// The place of the member of a union whose shape the value has.
fn member(v: &Value, shapes: &Shapes, members: &[(u32, u32)]) -> Result<usize, Untreeable> {
    let fits = |shape: u32| match (&shapes.shapes[shape as usize], v) {
        (
            Shape::Record { name: Some(n), .. } | Shape::Inline { name: Some(n), .. },
            Value::Record(r, _),
        ) => n == r,
        (Shape::Tag(n), Value::Tag(t)) => n == t,
        (Shape::Tag(n), Value::Bool(b)) => n == if *b { "True" } else { "False" },
        (Shape::Number(_), Value::Int(_) | Value::CodePoint(_)) => true,
        (Shape::Str, Value::Str(_)) | (Shape::Bytes, Value::Bytes(_)) => true,
        (Shape::List(_), Value::List(_)) => true,
        _ => false,
    };
    members
        .iter()
        .position(|&(_, m)| fits(m))
        .ok_or_else(|| format!("{v:?} is no member"))
}

fn field<'v>(v: &'v Value, name: &str) -> Result<&'v Value, Untreeable> {
    let Value::Record(r, fields) = v else {
        return Err(format!("{v:?} has no field {name}"));
    };
    fields
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, v)| v)
        .ok_or_else(|| format!("{r} has no field {name}"))
}

/// A tree from its bytes, as the codec reads a value of the shape of
/// `Tree`. The bytes are untrusted: whatever they hold, decoding ends
/// with a value or an error.
pub fn decode_tree(db: &dyn Db, program: Program, bytes: &[u8]) -> Result<Value, Untreeable> {
    decode_transport(db, program, "Tree", bytes)
}

/// A value of the type `name` of `std.transport` from untrusted bytes, as
/// `decode_tree` reads a tree.
pub fn decode_transport(
    db: &dyn Db,
    program: Program,
    name: &str,
    bytes: &[u8],
) -> Result<Value, Untreeable> {
    let ty = transport_type(db, program, name).ok_or("a program without std.transport")?;
    let (shapes, root) = shapes(db, program, ty);
    let mut reader = Reader::new(bytes);
    let value = decode(&mut reader, &shapes, root, 0)?;
    if !reader.is_empty() {
        return Err(format!("bytes after the {name}"));
    }
    Ok(value)
}

/// How deep a decoded tree may nest, so that forged bytes cannot exhaust
/// the stack.
const DEPTH: u32 = 2000;

type Reader<'a> = wire::Reader<'a, Untreeable>;

/// A length, in a word, which no more bytes than are left can hold.
fn count(r: &mut Reader) -> Result<usize, Untreeable> {
    let n = r.u64()?;
    match usize::try_from(n) {
        Ok(n) if n <= r.len() => Ok(n),
        _ => Err("a length past the end of the bytes".into()),
    }
}

fn decode(r: &mut Reader, shapes: &Shapes, shape: u32, depth: u32) -> Result<Value, Untreeable> {
    if depth > DEPTH {
        return Err("a tree nested too deeply".into());
    }
    if let Some(stored) = shapes.plain(shape) {
        let Shape::Stored {
            form, size, slots, ..
        } = &shapes.shapes[stored as usize]
        else {
            return Err(format!("shape {stored} is no storage form"));
        };
        let bytes = r.take(*size as usize)?;
        let mut register = vec![0u64; register_words(shapes, *form)];
        crag_abi::widen(slots, bytes, &mut register);
        return from_words(&register, shapes, *form);
    }
    let depth = depth + 1;
    Ok(match &shapes.shapes[shape as usize] {
        Shape::Unit => Value::List(Vec::new()),
        Shape::Tag(n) => Value::Tag(Cow::Owned(n.clone())),
        Shape::Number(crag_abi::Number::CodePoint) => {
            let c = u32::try_from(r.u64()?).ok().and_then(char::from_u32);
            Value::CodePoint(c.ok_or("a code point out of range")?)
        }
        Shape::Number(_) => Value::Int(r.u64()? as i64),
        Shape::Union { members, .. } | Shape::Variant { members, .. } => {
            let at = r.u32()? as usize;
            let &(_, member) = members.get(at).ok_or("a union member out of range")?;
            decode(r, shapes, member, depth)?
        }
        Shape::Record { name, fields } => {
            if name.is_some() {
                let identity: [u8; 16] = r.array()?;
                if shapes.identity(shape) != Some(identity) {
                    return Err("a record of another type".into());
                }
            }
            let mut out = Vec::new();
            for f in fields {
                let field = match &shapes.shapes[f.shape as usize] {
                    Shape::Stored { form, .. } => *form,
                    _ => f.shape,
                };
                out.push((Cow::Owned(f.name.clone()), decode(r, shapes, field, depth)?));
            }
            let name = name.clone().map_or(Cow::Borrowed(""), Cow::Owned);
            Value::Record(name, out)
        }
        Shape::Inline { name, fields, .. } => {
            let mut out = Vec::new();
            for f in fields {
                out.push((
                    Cow::Owned(f.name.clone()),
                    decode(r, shapes, f.shape, depth)?,
                ));
            }
            let name = name.clone().map_or(Cow::Borrowed(""), Cow::Owned);
            Value::Record(name, out)
        }
        &Shape::List(element) => {
            let element = match &shapes.shapes[element as usize] {
                Shape::Stored { form, .. } => *form,
                _ => element,
            };
            let n = count(r)?;
            let mut items = Vec::new();
            for _ in 0..n {
                items.push(decode(r, shapes, element, depth)?);
            }
            Value::List(items)
        }
        Shape::Str => {
            let n = count(r)?;
            let s = std::str::from_utf8(r.take(n)?).map_err(|_| "a string that is no UTF-8")?;
            Value::Str(s.to_string())
        }
        Shape::Bytes => {
            let n = count(r)?;
            Value::Bytes(r.take(n)?.to_vec())
        }
        s => return Err(format!("a tree holds no {s:?}")),
    })
}

/// How many words the register form of a shape takes.
fn register_words(shapes: &Shapes, shape: u32) -> usize {
    match &shapes.shapes[shape as usize] {
        Shape::Unit | Shape::Tag(_) => 0,
        Shape::Union { words, .. } | Shape::Variant { words, .. } => (*words as usize).max(1),
        Shape::Inline { words, .. } => *words as usize,
        _ => 1,
    }
}

/// A Plain value from its register form, the inverse of `words`.
fn from_words(w: &[u64], shapes: &Shapes, shape: u32) -> Result<Value, Untreeable> {
    let word = |i: usize| w.get(i).copied().ok_or("a register form too short");
    Ok(match &shapes.shapes[shape as usize] {
        Shape::Unit => Value::List(Vec::new()),
        Shape::Tag(n) => Value::Tag(Cow::Owned(n.clone())),
        Shape::Number(crag_abi::Number::CodePoint) => {
            let c = u32::try_from(word(0)?).ok().and_then(char::from_u32);
            Value::CodePoint(c.ok_or("a code point out of range")?)
        }
        Shape::Number(_) => Value::Int(word(0)? as i64),
        Shape::Union { members, .. } | Shape::Variant { members, .. } => {
            let index = word(0)?;
            let &(_, member) = members
                .iter()
                .find(|(i, _)| u64::from(*i) == index)
                .ok_or("a union member out of range")?;
            from_words(w.get(1..).unwrap_or_default(), shapes, member)?
        }
        Shape::Inline { name, fields, .. } => {
            let mut out = Vec::new();
            for f in fields {
                let at = f.offset as usize;
                let rest = w.get(at..).ok_or("a register form too short")?;
                out.push((
                    Cow::Owned(f.name.clone()),
                    from_words(rest, shapes, f.shape)?,
                ));
            }
            let name = name.clone().map_or(Cow::Borrowed(""), Cow::Owned);
            Value::Record(name, out)
        }
        s => return Err(format!("{s:?} in a register form")),
    })
}

/// The tree of a closure literal or a named function that becomes an
/// `Expr` in the body of `owner`, the type parameters of `generic` put
/// in, and its content hash: the hash of its bytes.
pub fn expr_tree<'db>(
    db: &'db dyn Db,
    program: Program,
    owner: Owner<'db>,
    expr: ExprId,
    generic: Option<(ItemId<'db>, &[Ty<'db>])>,
) -> Result<([u8; 32], Vec<u8>), Untreeable> {
    let tree = expr_tree_value(db, program, owner, expr, generic)?;
    let bytes = encode_tree(db, program, &tree)?;
    Ok((*blake3::hash(&bytes).as_bytes(), bytes))
}

/// The tree `expr_tree` encodes, as a value.
pub fn expr_tree_value<'db>(
    db: &'db dyn Db,
    program: Program,
    owner: Owner<'db>,
    expr: ExprId,
    generic: Option<(ItemId<'db>, &[Ty<'db>])>,
) -> Result<Value, Untreeable> {
    let mut helpers = Vec::new();
    let body = hir_body(db, program, owner);
    let types = body_types(db, program, owner);
    let mut cx = Reify::new(db, program, body, types, &mut helpers, true);
    cx.generic = generic.map(|(item, args)| (item, args.to_vec()));
    let root = match body.expr(expr) {
        Expr::Closure {
            params,
            body: inner,
        } => cx.closure(expr, params, *inner)?,
        Expr::Name { .. } => cx.reference(expr)?,
        _ => return Err("an expression that is no closure or function".into()),
    };
    let mut captures = Vec::new();
    for b in cx.captures.clone() {
        let ty = cx.types.binding(b).ok_or("a capture without a type")?;
        captures.push(cx.type_node(ty)?);
    }
    for v in cx.module_values.clone() {
        let ty = value_type(db, program, v).ok_or("a module value without a type")?;
        captures.push(cx.type_node(ty)?);
    }
    tree(db, program, root, captures, &mut helpers, true)
}

/// The tree with its helpers, each reified once, those they reach too.
fn tree<'db>(
    db: &'db dyn Db,
    program: Program,
    root: Value,
    captures: Vec<Value>,
    helpers: &mut Vec<ItemId<'db>>,
    hashes: bool,
) -> Result<Value, Untreeable> {
    let mut bundled = Vec::new();
    while bundled.len() < helpers.len() {
        let function = helpers[bundled.len()];
        bundled.push(helper(db, program, function, helpers, hashes)?);
    }
    Ok(record(
        "Tree",
        vec![
            ("version", Value::Int(TREE_VERSION)),
            ("root", root),
            ("helpers", Value::List(bundled)),
            ("captures", Value::List(captures)),
        ],
    ))
}

/// A function the tree bundles: its signature and body.
fn helper<'db>(
    db: &'db dyn Db,
    program: Program,
    function: ItemId<'db>,
    helpers: &mut Vec<ItemId<'db>>,
    hashes: bool,
) -> Result<Value, Untreeable> {
    let owner = Owner::Item(function);
    let body = hir_body(db, program, owner);
    let types = body_types(db, program, owner);
    let mut cx = Reify::new(db, program, body, types, helpers, hashes);
    let sig = signature(db, program, function);
    let params = cx.fn_params(&body.params)?;
    let result = result_type(db, program, function).ok_or("a helper without a result type")?;
    let root = body.root.ok_or("a helper without a body")?;
    Ok(record(
        "Helper",
        vec![
            ("typeParams", int(sig.type_params)),
            ("params", Value::List(params)),
            ("result", cx.type_node(result)?),
            ("body", cx.node(root)?),
        ],
    ))
}

/// The hash of a function's body as a tree, with the helpers it reaches
/// and without the body hashes of the `pub` functions it calls, so the
/// Exact policy compares a callee alone (§18.7).
#[crag_db::tracked(returns(copy))]
pub fn body_hash<'db>(db: &'db dyn Db, program: Program, function: ItemId<'db>) -> [u8; 32] {
    // A function of the prelude without a body is the compiler's own,
    // and hashes by its declaration.
    if hir_body(db, program, Owner::Item(function)).root.is_none() {
        let module = function.module(db);
        let decl = item_tree(db, *module)
            .items
            .iter()
            .find(|i| i.id == function)
            .map(|i| i.signature.text())
            .unwrap_or_default();
        let text = format!("{}\n{decl}", module.path(db));
        return *blake3::hash(text.as_bytes()).as_bytes();
    }
    let tree = || -> Result<Vec<u8>, Untreeable> {
        let mut helpers = vec![function];
        let root = record("HelperRef", vec![("index", Value::Int(0))]);
        let root = record(
            "Closure",
            vec![("params", Value::List(Vec::new())), ("body", root)],
        );
        let tree = tree(db, program, root, Vec::new(), &mut helpers, false)?;
        encode_tree(db, program, &tree)
    };
    // A function the tree cannot hold yet hashes by its declaration,
    // which a receiver can only match by its signature.
    let bytes = tree().unwrap_or_else(|e| e.into_bytes());
    *blake3::hash(&bytes).as_bytes()
}

/// The reifying of one body.
struct Reify<'a, 'db> {
    db: &'db dyn Db,
    program: Program,
    body: &'a Body<'db>,
    types: &'a InferenceResult<'db>,
    helpers: &'a mut Vec<ItemId<'db>>,
    /// Whether references carry their callees' body hashes.
    hashes: bool,
    /// The type arguments the body's type parameters stand for.
    generic: Option<(ItemId<'db>, Vec<Ty<'db>>)>,
    locals: Vec<(BindingId, i64)>,
    captures: Vec<BindingId>,
    /// The module values the root closure reads, captured after its
    /// bindings (§18.6).
    module_values: Vec<ItemId<'db>>,
}

impl<'a, 'db> Reify<'a, 'db> {
    fn new(
        db: &'db dyn Db,
        program: Program,
        body: &'a Body<'db>,
        types: &'a InferenceResult<'db>,
        helpers: &'a mut Vec<ItemId<'db>>,
        hashes: bool,
    ) -> Self {
        Reify {
            db,
            program,
            body,
            types,
            helpers,
            hashes,
            generic: None,
            locals: Vec::new(),
            captures: Vec::new(),
            module_values: Vec::new(),
        }
    }

    /// The local a binding introduces, numbered at its first introduction.
    fn bind(&mut self, binding: BindingId) -> Value {
        if let Some(&(_, i)) = self.locals.iter().find(|(b, _)| *b == binding) {
            return Value::Int(i);
        }
        let i = self.locals.len() as i64;
        self.locals.push((binding, i));
        Value::Int(i)
    }

    /// The root closure: its free bindings are the captures.
    fn closure(
        &mut self,
        frame: ExprId,
        params: &[crag_hir::ClosureParam],
        inner: ExprId,
    ) -> Result<Value, Untreeable> {
        for b in self.body.free_bindings(frame) {
            match self.body.binding(b).kind {
                BindingKind::Fn => return Err("a captured local function in a tree".into()),
                _ => self.captures.push(b),
            }
        }
        self.module_values = module_values(self.body, frame)
            .into_iter()
            .map(|(v, _)| v)
            .collect();
        self.closure_value(params, inner)
    }

    fn closure_value(
        &mut self,
        params: &[crag_hir::ClosureParam],
        inner: ExprId,
    ) -> Result<Value, Untreeable> {
        let mut out = Vec::new();
        for p in params {
            let pat = self.pat(p.pat)?;
            let ty = p.ty.map(|t| self.written(t)).transpose()?;
            out.push(record(
                "ClosureParam",
                vec![("pat", pat), ("ty", option(ty))],
            ));
        }
        Ok(record(
            "Closure",
            vec![("params", Value::List(out)), ("body", self.node(inner)?)],
        ))
    }

    /// A named function as the root: a closure that calls it.
    fn reference(&mut self, expr: ExprId) -> Result<Value, Untreeable> {
        let ty = self.types.expr(expr).ok_or("a function without a type")?;
        let (params, ..) = ty.as_fn(self.db).ok_or("a function of no function type")?;
        let callee = self.callee_node(expr)?;
        let mut pats = Vec::new();
        let mut args = Vec::new();
        for i in 0..params.len() {
            let local = Value::Int(i as i64);
            pats.push(record(
                "ClosureParam",
                vec![
                    (
                        "pat",
                        record(
                            "Bind",
                            vec![("local", local.clone()), ("sub", option(None))],
                        ),
                    ),
                    ("ty", option(None)),
                ],
            ));
            args.push(record("LocalRef", vec![("index", local)]));
        }
        let call = call(callee.0, callee.1, args, Vec::new());
        Ok(record(
            "Closure",
            vec![("params", Value::List(pats)), ("body", call)],
        ))
    }

    fn fn_params(&mut self, params: &[crag_hir::Param]) -> Result<Vec<Value>, Untreeable> {
        let mut out = Vec::new();
        for p in params {
            let local = self.bind(p.binding);
            let ty = self.written(p.ty)?;
            let default = p.default.map(|d| self.node(d)).transpose()?;
            out.push(record(
                "FnParam",
                vec![("local", local), ("ty", ty), ("default", option(default))],
            ));
        }
        Ok(out)
    }

    fn nodes(&mut self, exprs: &[ExprId]) -> Result<Value, Untreeable> {
        let nodes = exprs
            .iter()
            .map(|&e| self.node(e))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Value::List(nodes))
    }

    fn node(&mut self, id: ExprId) -> Result<Value, Untreeable> {
        let db = self.db;
        Ok(match self.body.expr(id) {
            Expr::Missing => return Err("an expression with errors".into()),
            Expr::Hole | Expr::Embed | Expr::Atomic(_) => {
                return Err("a form a tree may not hold".into());
            }
            // A literal written with its sign keeps it (§6.2.1).
            Expr::Literal(l) => signed(lit(l), self.body.is_negative(id)),
            Expr::Str(parts) => {
                let mut out = Vec::new();
                for part in parts {
                    out.push(match part {
                        StrPart::Text(t) => text(t),
                        StrPart::Expr(e) => self.node(*e)?,
                    });
                }
                record("Text", vec![("parts", Value::List(out))])
            }
            Expr::Name {
                local: Some(binding),
                ..
            } => self.local(*binding)?,
            Expr::Name {
                item: Some(Resolution::Type(_)),
                ..
            } => {
                let ty = self.types.expr(id).ok_or("a type without a type")?;
                self.type_name(ty)?
            }
            Expr::Name {
                item: Some(Resolution::Value { value: None, .. }),
                ..
            } => {
                let (callee, targs) = self.callee_node(id)?;
                if !targs.is_empty() {
                    return Err("a generic function as a value".into());
                }
                callee
            }
            Expr::Name {
                item:
                    Some(Resolution::Value {
                        value: Some(value), ..
                    }),
                ..
            } => match self.module_values.iter().position(|v| v == value) {
                Some(k) => record("CaptureRef", vec![("index", int(self.captures.len() + k))]),
                None => return Err("a module value outside the root closure".into()),
            },
            Expr::Name { .. } => return Err("a name without a resolution".into()),
            Expr::Call {
                callee,
                args,
                fields,
            } => {
                let fields = self.fields(fields.as_deref())?;
                let args = self.nodes(args)?;
                let Value::List(args) = args else {
                    unreachable!()
                };
                match self.types.callee(id) {
                    Some(Callee::Value) => {
                        let callee = self.node(*callee)?;
                        call(callee, Vec::new(), args, fields)
                    }
                    Some(Callee::Construct(ty) | Callee::Refine(ty)) => {
                        let ty = self.type_name(*ty)?;
                        call(ty, Vec::new(), args, fields)
                    }
                    _ => {
                        let (callee, targs) = self.callee_node(id)?;
                        call(callee, targs, args, fields)
                    }
                }
            }
            Expr::MethodCall {
                receiver,
                name,
                optional,
                args,
                fields,
                ..
            } => {
                let receiver = self.node(*receiver)?;
                let fields = self.fields(fields.as_deref())?;
                let Value::List(rest) = self.nodes(args)? else {
                    unreachable!()
                };
                match self.types.callee(id) {
                    Some(Callee::Value) => {
                        let f = field_node(receiver, name.text(db), *optional);
                        call(f, Vec::new(), rest, fields)
                    }
                    _ if *optional => return Err("an optional call in a tree".into()),
                    Some(Callee::Function(_) | Callee::Instance(_)) => {
                        let (callee, targs) = self.callee_node(id)?;
                        let args = std::iter::once(receiver).chain(rest).collect();
                        call(callee, targs, args, fields)
                    }
                    _ => return Err("a call a tree cannot hold yet".into()),
                }
            }
            Expr::TypedCall { args, fields, .. } => {
                let fields = self.fields(fields.as_deref())?;
                let Value::List(args) = self.nodes(args)? else {
                    unreachable!()
                };
                let (callee, targs) = self.callee_node(id)?;
                call(callee, targs, args, fields)
            }
            Expr::Field {
                receiver,
                name,
                optional,
                ..
            } => {
                let receiver = self.node(*receiver)?;
                match self.types.callee(id) {
                    None => field_node(receiver, name.text(db), *optional),
                    Some(_) if *optional => return Err("an optional call in a tree".into()),
                    Some(_) => {
                        let (callee, targs) = self.callee_node(id)?;
                        call(callee, targs, vec![receiver], Vec::new())
                    }
                }
            }
            Expr::Index { base, args } => record(
                "Index",
                vec![("base", self.node(*base)?), ("args", self.nodes(args)?)],
            ),
            Expr::TypeArgs { .. } => return Err("type arguments as a value".into()),
            Expr::And(a, b) => record(
                "And",
                vec![("left", self.node(*a)?), ("right", self.node(*b)?)],
            ),
            Expr::Or(a, b) => record(
                "Or",
                vec![("left", self.node(*a)?), ("right", self.node(*b)?)],
            ),
            Expr::Not(a) => record("Not", vec![("value", self.node(*a)?)]),
            Expr::Range { start, end } => {
                let start = self.node(*start)?;
                let end = end.map(|e| self.node(e)).transpose()?;
                record("RangeNode", vec![("start", start), ("end", option(end))])
            }
            Expr::Is { expr, ty } => record(
                "Is",
                vec![("value", self.node(*expr)?), ("ty", self.written(*ty)?)],
            ),
            Expr::Record(fields) => {
                let fields = self.fields(Some(fields))?;
                record("RecordNode", vec![("fields", Value::List(fields))])
            }
            Expr::List(items) => record("ListNode", vec![("items", self.nodes(items)?)]),
            Expr::Map(entries) => {
                let mut out = Vec::new();
                for &(k, v) in entries {
                    out.push(record(
                        "Entry",
                        vec![("key", self.node(k)?), ("value", self.node(v)?)],
                    ));
                }
                record("MapNode", vec![("entries", Value::List(out))])
            }
            Expr::Grid(rows) => {
                let rows = rows
                    .iter()
                    .map(|r| self.nodes(r))
                    .collect::<Result<Vec<_>, _>>()?;
                record("GridNode", vec![("rows", Value::List(rows))])
            }
            Expr::Block { stmts, tail } => {
                let mut out = Vec::new();
                for stmt in stmts {
                    out.push(self.stmt(stmt)?);
                }
                let tail = tail.map(|t| self.node(t)).transpose()?;
                record(
                    "Block",
                    vec![("stmts", Value::List(out)), ("tail", option(tail))],
                )
            }
            Expr::Closure { params, body } => self.closure_value(params, *body)?,
            Expr::If {
                condition,
                then,
                otherwise,
            } => {
                let condition = self.node(*condition)?;
                let then = self.node(*then)?;
                let otherwise = otherwise.map(|o| self.node(o)).transpose()?;
                record(
                    "If",
                    vec![
                        ("condition", condition),
                        ("then", then),
                        ("otherwise", option(otherwise)),
                    ],
                )
            }
            Expr::Case { subject, arms } => {
                let subject = self.node(*subject)?;
                let mut out = Vec::new();
                for arm in arms {
                    let pat = self.pat(arm.pat)?;
                    let guard = arm.guard.map(|g| self.node(g)).transpose()?;
                    let body = self.node(arm.body)?;
                    out.push(record(
                        "Arm",
                        vec![("pat", pat), ("guard", option(guard)), ("body", body)],
                    ));
                }
                record(
                    "Case",
                    vec![("subject", subject), ("arms", Value::List(out))],
                )
            }
            Expr::Pass => tag("Pass"),
            Expr::Lazy(inner) => record("LazyNode", vec![("value", self.node(*inner)?)]),
        })
    }

    fn local(&mut self, binding: BindingId) -> Result<Value, Untreeable> {
        if let Some(i) = self.captures.iter().position(|&b| b == binding) {
            return Ok(record("CaptureRef", vec![("index", int(i))]));
        }
        match self.locals.iter().find(|(b, _)| *b == binding) {
            Some(&(_, i)) => Ok(record("LocalRef", vec![("index", Value::Int(i))])),
            None => Err("a binding from outside the tree".into()),
        }
    }

    /// The callee an expression's call or value names, and its type
    /// arguments.
    fn callee_node(&mut self, id: ExprId) -> Result<(Value, Vec<Value>), Untreeable> {
        let (function, args) = match self.types.callee(id) {
            Some(Callee::Function(f)) => (*f, Vec::new()),
            Some(Callee::Instance(instance)) => (instance.function, instance.args.clone()),
            _ => return Err("a call a tree cannot hold yet".into()),
        };
        let targs = args
            .into_iter()
            .map(|t| self.type_node(t))
            .collect::<Result<Vec<_>, _>>()?;
        Ok((self.function(function)?, targs))
    }

    /// A `pub` function by its reference, any other as a helper.
    fn function(&mut self, f: ItemId<'db>) -> Result<Value, Untreeable> {
        let db = self.db;
        if !is_public(db, f) {
            let index = match self.helpers.iter().position(|&h| h == f) {
                Some(i) => i,
                None => {
                    self.helpers.push(f);
                    self.helpers.len() - 1
                }
            };
            return Ok(record("HelperRef", vec![("index", int(index))]));
        }
        let sig = signature(db, self.program, f);
        let params = sig
            .params
            .iter()
            .map(|p| self.type_node(p.ty))
            .collect::<Result<Vec<_>, _>>()?;
        let result = result_type(db, self.program, f).ok_or("a callee without a result type")?;
        let pure = function_effects(db, self.program, f).is_empty();
        let signature = record(
            "FnType",
            vec![
                ("params", Value::List(params)),
                ("result", self.type_node(result)?),
                ("pure", Value::Bool(pure)),
            ],
        );
        let hash = match self.hashes {
            true => body_hash(db, self.program, f).to_vec(),
            false => Vec::new(),
        };
        let module = f.module(db).path(db);
        let (package, major) = package(db, self.program, module);
        let reference = record(
            "FnRef",
            vec![
                ("package", text(&package)),
                ("major", int(major)),
                ("module", text(module)),
                ("name", text(f.name(db).text(db))),
                ("signature", signature),
                ("body", Value::Bytes(hash)),
            ],
        );
        Ok(record("Function", vec![("target", reference)]))
    }

    fn fields(&mut self, fields: Option<&[FieldArg<'db>]>) -> Result<Vec<Value>, Untreeable> {
        let mut out = Vec::new();
        for f in fields.unwrap_or_default() {
            out.push(match f {
                FieldArg::Field { path, value } => {
                    let path = path.iter().map(|n| text(n.text(self.db))).collect();
                    record(
                        "FieldArg",
                        vec![("path", Value::List(path)), ("value", self.node(*value)?)],
                    )
                }
                FieldArg::Spread(value) => record("Spread", vec![("value", self.node(*value)?)]),
            });
        }
        Ok(out)
    }

    fn stmt(&mut self, stmt: &Stmt) -> Result<Value, Untreeable> {
        Ok(match stmt {
            Stmt::Expr(e) => record("ExprStmt", vec![("value", self.node(*e)?)]),
            Stmt::Let { pat, ty, value } => {
                let value = self.node(*value)?;
                let ty = ty.map(|t| self.written(t)).transpose()?;
                let pat = self.pat(*pat)?;
                record(
                    "Let",
                    vec![("pat", pat), ("ty", option(ty)), ("value", value)],
                )
            }
            Stmt::LetElse {
                pat,
                ty,
                value,
                rest,
                otherwise,
            } => {
                let value = self.node(*value)?;
                let ty = ty.map(|t| self.written(t)).transpose()?;
                let pat = self.pat(*pat)?;
                let rest = rest.map(|r| self.pat(r)).transpose()?;
                let otherwise = self.node(*otherwise)?;
                record(
                    "LetElse",
                    vec![
                        ("pat", pat),
                        ("ty", option(ty)),
                        ("value", value),
                        ("rest", option(rest)),
                        ("otherwise", otherwise),
                    ],
                )
            }
            Stmt::Bind { binding, ty, value } => {
                if self.body.binding(*binding).kind != BindingKind::Var {
                    return Err("a form a tree may not hold".into());
                }
                let value = self.node(*value)?;
                let ty = ty.map(|t| self.written(t)).transpose()?;
                let local = self.bind(*binding);
                record(
                    "Var",
                    vec![("local", local), ("ty", option(ty)), ("value", value)],
                )
            }
            Stmt::Assign { binding, value } => {
                let value = self.node(*value)?;
                let Value::Record(_, mut fields) = self.local(*binding)? else {
                    unreachable!("a local is a record");
                };
                let local = fields.remove(0).1;
                record("Assign", vec![("local", local), ("value", value)])
            }
            Stmt::For {
                pat,
                iterable,
                body,
            } => {
                let iterable = self.node(*iterable)?;
                let pat = self.pat(*pat)?;
                let body = self.node(*body)?;
                record(
                    "For",
                    vec![("pat", pat), ("iterable", iterable), ("body", body)],
                )
            }
            Stmt::Return(e) => {
                let value = e.map(|e| self.node(e)).transpose()?;
                record("Return", vec![("value", option(value))])
            }
            Stmt::Emit { .. } | Stmt::On { .. } => {
                return Err("a form a tree may not hold".into());
            }
            Stmt::Fn { binding, function } => {
                if function.generic {
                    return Err("a generic local function in a tree".into());
                }
                let local = self.bind(*binding);
                let params = self.fn_params(&function.params)?;
                let result = function.result.map(|t| self.written(t)).transpose()?;
                let body = function.body.ok_or("a local function without a body")?;
                record(
                    "LocalFn",
                    vec![
                        ("local", local),
                        ("params", Value::List(params)),
                        ("result", option(result)),
                        ("pure", Value::Bool(function.pure)),
                        ("body", self.node(body)?),
                    ],
                )
            }
        })
    }

    fn pat(&mut self, id: PatId) -> Result<Value, Untreeable> {
        Ok(match self.body.pat(id) {
            Pat::Missing => return Err("a pattern with errors".into()),
            Pat::Wildcard => tag("Wildcard"),
            Pat::Bind { binding, sub } => {
                let local = self.bind(*binding);
                let sub = sub.map(|s| self.pat(s)).transpose()?;
                record("Bind", vec![("local", local), ("sub", option(sub))])
            }
            Pat::Type(t) => record("TypePat", vec![("ty", self.written(*t)?)]),
            Pat::Record { ty, fields } => {
                let ty = ty.map(|t| self.written(t)).transpose()?;
                let mut out = Vec::new();
                for f in fields {
                    let name = f.name.map(|n| text(n.text(self.db)));
                    let pat = self.pat(f.pat)?;
                    out.push(record(
                        "PatField",
                        vec![("name", option(name)), ("pat", pat)],
                    ));
                }
                record(
                    "RecordPat",
                    vec![("ty", option(ty)), ("fields", Value::List(out))],
                )
            }
            Pat::List {
                before,
                rest,
                after,
            } => {
                let before = before
                    .iter()
                    .map(|&p| self.pat(p))
                    .collect::<Result<Vec<_>, _>>()?;
                let rest = rest.map(|r| {
                    let local = r.map(|b| self.bind(b));
                    record("Rest", vec![("local", option(local))])
                });
                let after = after
                    .iter()
                    .map(|&p| self.pat(p))
                    .collect::<Result<Vec<_>, _>>()?;
                record(
                    "ListPat",
                    vec![
                        ("before", Value::List(before)),
                        ("rest", option(rest)),
                        ("after", Value::List(after)),
                    ],
                )
            }
            Pat::Literal(l) => lit_pat(l),
            Pat::Range { start, end } => record(
                "RangePat",
                vec![("start", lit_pat(start)), ("end", lit_pat(end))],
            ),
            Pat::Or(alternatives) => {
                let alternatives = alternatives
                    .iter()
                    .map(|&p| self.pat(p))
                    .collect::<Result<Vec<_>, _>>()?;
                record("OrPat", vec![("alternatives", Value::List(alternatives))])
            }
        })
    }

    /// A written type, as inference lowered it.
    fn written(&mut self, id: TypeRefId) -> Result<Value, Untreeable> {
        let ty = self
            .types
            .types
            .get(id.index())
            .copied()
            .flatten()
            .ok_or("a written type without a type")?;
        self.type_node(ty)
    }

    fn type_name(&mut self, ty: Ty<'db>) -> Result<Value, Untreeable> {
        Ok(record("TypeName", vec![("ty", self.type_node(ty)?)]))
    }

    /// A type, spelled out, the type parameters of `generic` put in.
    fn type_node(&mut self, ty: Ty<'db>) -> Result<Value, Untreeable> {
        let ty = match &self.generic {
            Some((item, args)) => subst(self.db, self.program, ty, *item, args),
            None => ty,
        };
        type_value(self.db, self.program, ty)
    }
}

/// A type, spelled out: a named type by its reference.
pub fn type_value<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
) -> Result<Value, Untreeable> {
    let list = |types: &[Ty<'db>]| -> Result<Value, Untreeable> {
        let nodes = types
            .iter()
            .map(|&t| type_value(db, program, t))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Value::List(nodes))
    };
    Ok(match ty.kind(db) {
        TyKind::Error => return Err("a type with errors".into()),
        TyKind::Builtin(b, args) => {
            let args = match b {
                Builtin::Fixed(scale) => {
                    Value::List(vec![record("Scale", vec![("digits", int(*scale))])])
                }
                _ => list(args)?,
            };
            let module = match b {
                Builtin::Expr => "std.transport",
                Builtin::RuntimeStream | Builtin::RuntimeHub => "std.stream",
                Builtin::RuntimeSocket => "std.io",
                Builtin::CF32 | Builtin::CPtr | Builtin::COut => "std.c",
                _ => crag_hir::PRELUDE,
            };
            type_ref(db, program, ty, module, b.name(), args)
        }
        TyKind::Named(item, args) => {
            let args = list(args)?;
            type_ref(
                db,
                program,
                ty,
                item.module(db).path(db),
                item.name(db).text(db),
                args,
            )
        }
        TyKind::Record { fields, open } if fields.is_empty() && !open => tag("UnitType"),
        TyKind::Record { fields, open } => {
            let mut out = Vec::new();
            for (name, t) in fields {
                out.push(record(
                    "TypeField",
                    vec![
                        ("name", text(name.text(db))),
                        ("ty", type_value(db, program, *t)?),
                    ],
                ));
            }
            record(
                "RecordType",
                vec![("fields", Value::List(out)), ("open", Value::Bool(*open))],
            )
        }
        TyKind::Fn {
            params,
            result,
            pure,
        } => record(
            "FnType",
            vec![
                ("params", list(params)?),
                ("result", type_value(db, program, *result)?),
                ("pure", Value::Bool(*pure)),
            ],
        ),
        TyKind::Union(members) => {
            let mut members = members.clone();
            members.sort_by_key(|&m| type_hash(db, program, m));
            record("UnionType", vec![("members", list(&members)?)])
        }
        TyKind::Param(_, index, _) => record("TypeParam", vec![("index", int(*index))]),
    })
}

fn type_ref(
    db: &dyn Db,
    program: Program,
    ty: Ty<'_>,
    module: &str,
    name: &str,
    args: Value,
) -> Value {
    let (package, major) = package(db, program, module);
    let hash = type_hash(db, program, ty).0.to_vec();
    let reference = record(
        "TypeRef",
        vec![
            ("package", text(&package)),
            ("major", int(major)),
            ("module", text(module)),
            ("name", text(name)),
            ("args", args),
            ("hash", Value::Bytes(hash)),
        ],
    );
    record("Named", vec![("ty", reference)])
}

fn call(callee: Value, targs: Vec<Value>, args: Vec<Value>, fields: Vec<Value>) -> Value {
    record(
        "Call",
        vec![
            ("callee", callee),
            ("typeArgs", Value::List(targs)),
            ("args", Value::List(args)),
            ("fields", Value::List(fields)),
        ],
    )
}

fn field_node(receiver: Value, name: &str, optional: bool) -> Value {
    record(
        "Field",
        vec![
            ("receiver", receiver),
            ("name", text(name)),
            ("optional", Value::Bool(optional)),
        ],
    )
}

/// A number literal with a `-` before its digits.
fn signed(lit: Value, negative: bool) -> Value {
    match lit {
        Value::Record(name, mut fields) if negative => {
            if let Some((_, Value::Str(digits))) = fields.first_mut() {
                digits.insert(0, '-');
            }
            Value::Record(name, fields)
        }
        lit => lit,
    }
}

fn lit(l: &Literal) -> Value {
    match l {
        Literal::Int(n) => record("IntLit", vec![("digits", text(&n.to_string()))]),
        Literal::Float(d) => record("FloatLit", vec![("digits", text(d))]),
        Literal::Str(s) => record("StrLit", vec![("value", text(s))]),
        Literal::Bytes(b) => record("BytesLit", vec![("value", Value::Bytes(b.clone()))]),
        Literal::CodePoint(c) => record("CodePointLit", vec![("value", Value::CodePoint(*c))]),
    }
}

fn lit_pat(l: &PatLiteral) -> Value {
    record(
        "LitPat",
        vec![
            ("negative", Value::Bool(l.negative)),
            ("lit", lit(&l.literal)),
        ],
    )
}

/// The package a module belongs to and its major version: `std` and a
/// loose module belong to none and name their first segment.
fn package(db: &dyn Db, program: Program, module: &str) -> (String, u32) {
    match program.packages(db).of(module) {
        Some(p) => (p.name.clone(), p.major),
        None => (module.split('.').next().unwrap_or("").to_string(), 0),
    }
}
