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

//! The MIR: a control-flow graph of basic blocks over typed locals.
//!
//! Locals are not in SSA form: a block may assign any local. A local holds
//! one value of its type; when that type is counted, the local owns one
//! reference while it is live. An operand that is a local gives that
//! reference away, and a place only borrows the local it starts at.

use crag_db::Db;
use crag_hir::{BindingId, ExprId, ItemId, Name, Owner};
use crag_types::{Builtin, Step, Ty, TyKind};

use crate::{Entry, InstanceKey};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, crag_db::SalsaValue)]
pub struct Local(pub u32);

/// Index into `MirBody::blocks`. Block 0 is where execution starts, and
/// no terminator goes back to it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, crag_db::SalsaValue)]
pub struct BlockId(pub u32);

impl Local {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl BlockId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct MirBody<'db> {
    /// Locals `0..params` hold the parameters on entry.
    pub params: usize,
    /// Whether the code is called as a function value, so that local 0 is
    /// its environment: one word, a box or null (§11.5.9).
    pub env: bool,
    pub locals: Vec<LocalDecl<'db>>,
    pub blocks: Vec<Block<'db>>,
    pub result: Ty<'db>,
    /// `Bool`, the type of the flags checks compute.
    pub bool_ty: Ty<'db>,
    /// What the builder does not lower yet; each traps where it is
    /// reached.
    pub unsupported: Vec<(ExprId, &'static str)>,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct LocalDecl<'db> {
    pub ty: Ty<'db>,
    /// The binding it holds; none for a temporary.
    pub binding: Option<(BindingId, Name<'db>)>,
    /// Whether its values are reference-counted.
    pub counted: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Block<'db> {
    pub statements: Vec<Statement<'db>>,
    pub terminator: Terminator<'db>,
}

/// A local, or a part of the value in it.
#[derive(Clone, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub struct Place<'db> {
    pub local: Local,
    /// Never a `Slice`, which makes a new list.
    pub path: Vec<Step<'db>>,
}

impl<'db> Place<'db> {
    pub fn local(local: Local) -> Place<'db> {
        Place {
            local,
            path: Vec::new(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum Operand<'db> {
    Local(Local),
    Const(Constant<'db>),
}

/// A constant, typed by where it goes.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum Constant<'db> {
    /// A value of an integer type or a `CodePoint`, or of a `Fixed` in
    /// units of its scale.
    Int(i128),
    /// By its bits.
    Float(u64),
    Str(String),
    Bytes(Vec<u8>),
    /// The value of a tag type.
    Tag(Ty<'db>),
    Unit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum Rvalue<'db> {
    Use(Operand<'db>),
    /// A part of a value, borrowed from it.
    Read(Place<'db>),
    /// The operand as the type of the local it is assigned to: a type it
    /// fits, or a member of its union that a test has established.
    Convert(Operand<'db>),
    /// Arithmetic on a number type. With a check, the operation traps on
    /// overflow and on a zero divisor, at the expression; without one it
    /// is the machine's: integers wrap, and a `Float` follows IEEE 754.
    /// Checks become explicit operations before liveness (§3.1.1, §3.1.4).
    Binary {
        op: BinOp,
        ty: Builtin,
        a: Operand<'db>,
        b: Operand<'db>,
        check: Option<ExprId>,
    },
    /// Whether the integer operation overflows its type.
    Overflows {
        op: BinOp,
        ty: Builtin,
        a: Operand<'db>,
        b: Operand<'db>,
    },
    /// Whether any of these `Float` results overflowed. Code generation
    /// may read and clear the sticky overflow flag instead of testing each.
    FloatOverflow(Vec<Local>),
    /// A comparison of numbers or code points, or `Eq` and `Ne` of
    /// strings and bytes: a `Bool`.
    Compare {
        op: CmpOp,
        ty: Builtin,
        a: Operand<'db>,
        b: Operand<'db>,
    },
    /// A record, its fields in the order of `fields_of`.
    Record {
        ty: Ty<'db>,
        fields: Vec<(Name<'db>, Operand<'db>)>,
    },
    /// A list, or a set when the local is one.
    List(Vec<Operand<'db>>),
    Map(Vec<(Operand<'db>, Operand<'db>)>),
    /// Strings joined.
    Concat(Vec<Operand<'db>>),
    /// The number of elements of a list, an `Int`.
    Len(Place<'db>),
    /// An element of a list at an index known to lie inside it, borrowed.
    Index {
        list: Place<'db>,
        index: Operand<'db>,
    },
    /// The value of a map at a key, or `Empty`: an `Option`, borrowed.
    MapGet {
        map: Place<'db>,
        key: Operand<'db>,
    },
    /// A list without its first `front` and last `back` elements.
    Slice {
        list: Place<'db>,
        front: u32,
        back: u32,
    },
    /// The value of a module-level `let`.
    Global(ItemId<'db>),
    /// A function value: the code, and an environment of type `env`, a
    /// record of the captured values in its order, or null when there are
    /// none (§11.5.9). On the side stack the environment borrows the
    /// captured locals, which stay live while the value does; on the heap
    /// it takes their references.
    Closure {
        code: InstanceKey<'db>,
        env: Ty<'db>,
        captures: Vec<Operand<'db>>,
        placement: ClosurePlacement,
    },
    /// A function value of the code with an environment it already has:
    /// how a local function names itself.
    FnValue {
        code: InstanceKey<'db>,
        env: Operand<'db>,
    },
}

/// Where a closure's environment lives, by its escape level (§11.5.8).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum ClosurePlacement {
    /// In the frame's part of the side stack, uncounted, for a closure
    /// that does not outlive the frame.
    SideStack,
    /// In a counted box.
    Heap,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum Statement<'db> {
    /// The local must not occur in the rvalue.
    Assign(Local, Rvalue<'db>),
    /// Adds a reference to the value of a counted local.
    Retain(Local),
    /// Gives up the local's reference, freeing the value with the last.
    Release(Local),
    /// A point on a loop's back-edge where the runtime may stop the fiber.
    Poll,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum TrapKind {
    Overflow,
    DivideByZero,
    /// An index outside the list.
    Index,
    /// `???` (§6.11).
    Hole,
    /// No arm of a `case` matched, which checking rules out.
    NoMatch,
    /// The body has errors, reported where it was checked.
    Error,
    /// Something the builder does not lower yet.
    Unsupported,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum Terminator<'db> {
    Jump(BlockId),
    /// Goes to `then` if the `Bool` is `True`.
    Branch {
        cond: Operand<'db>,
        then: BlockId,
        otherwise: BlockId,
    },
    /// Goes to the first case whose type the value at the place has.
    Switch {
        place: Place<'db>,
        cases: Vec<(Ty<'db>, BlockId)>,
        otherwise: BlockId,
    },
    /// Calls a function and continues at `target` with its result in
    /// `dst`.
    Call {
        func: InstanceKey<'db>,
        args: Vec<Operand<'db>>,
        dst: Local,
        target: BlockId,
        site: ExprId,
    },
    /// A call that replaces this function's frame (§5.6.3).
    TailCall {
        func: InstanceKey<'db>,
        args: Vec<Operand<'db>>,
        site: ExprId,
    },
    /// A call of a function value, which goes with its environment, before
    /// the arguments, to its code.
    CallValue {
        callee: Operand<'db>,
        args: Vec<Operand<'db>>,
        dst: Local,
        target: BlockId,
        site: ExprId,
    },
    TailCallValue {
        callee: Operand<'db>,
        args: Vec<Operand<'db>>,
        site: ExprId,
    },
    Return(Operand<'db>),
    Trap {
        kind: TrapKind,
        site: Option<ExprId>,
    },
}

impl<'db> Terminator<'db> {
    pub fn successors(&self) -> Vec<BlockId> {
        match self {
            Terminator::Jump(b) => vec![*b],
            Terminator::Branch {
                then, otherwise, ..
            } => vec![*then, *otherwise],
            Terminator::Switch {
                cases, otherwise, ..
            } => cases.iter().map(|(_, b)| *b).chain([*otherwise]).collect(),
            Terminator::Call { target, .. } | Terminator::CallValue { target, .. } => vec![*target],
            Terminator::TailCall { .. }
            | Terminator::TailCallValue { .. }
            | Terminator::Return(_)
            | Terminator::Trap { .. } => Vec::new(),
        }
    }

    pub fn successors_mut(&mut self) -> Vec<&mut BlockId> {
        match self {
            Terminator::Jump(b) => vec![b],
            Terminator::Branch {
                then, otherwise, ..
            } => vec![then, otherwise],
            Terminator::Switch {
                cases, otherwise, ..
            } => cases
                .iter_mut()
                .map(|(_, b)| b)
                .chain([otherwise])
                .collect(),
            Terminator::Call { target, .. } | Terminator::CallValue { target, .. } => vec![target],
            Terminator::TailCall { .. }
            | Terminator::TailCallValue { .. }
            | Terminator::Return(_)
            | Terminator::Trap { .. } => Vec::new(),
        }
    }
}

impl Operand<'_> {
    fn locals_mut(&mut self) -> Option<&mut Local> {
        match self {
            Operand::Local(l) => Some(l),
            Operand::Const(_) => None,
        }
    }
}

impl<'db> Rvalue<'db> {
    /// Every local the rvalue mentions.
    pub fn locals_mut(&mut self) -> Vec<&mut Local> {
        let mut out = Vec::new();
        match self {
            Rvalue::Use(o) | Rvalue::Convert(o) | Rvalue::FnValue { env: o, .. } => {
                out.extend(o.locals_mut())
            }
            Rvalue::Read(p) | Rvalue::Len(p) | Rvalue::Slice { list: p, .. } => {
                out.push(&mut p.local)
            }
            Rvalue::Binary { a, b, .. }
            | Rvalue::Overflows { a, b, .. }
            | Rvalue::Compare { a, b, .. } => {
                out.extend(a.locals_mut());
                out.extend(b.locals_mut());
            }
            Rvalue::FloatOverflow(locals) => out.extend(locals.iter_mut()),
            Rvalue::Record { fields, .. } => {
                out.extend(fields.iter_mut().filter_map(|(_, o)| o.locals_mut()))
            }
            Rvalue::List(items) | Rvalue::Concat(items) => {
                out.extend(items.iter_mut().filter_map(Operand::locals_mut))
            }
            Rvalue::Map(entries) => {
                for (k, v) in entries {
                    out.extend(k.locals_mut());
                    out.extend(v.locals_mut());
                }
            }
            Rvalue::Index { list: p, index: o } | Rvalue::MapGet { map: p, key: o } => {
                out.push(&mut p.local);
                out.extend(o.locals_mut());
            }
            Rvalue::Closure { captures, .. } => {
                out.extend(captures.iter_mut().filter_map(Operand::locals_mut))
            }
            Rvalue::Global(_) => {}
        }
        out
    }
}

impl<'db> Statement<'db> {
    /// Every local the statement mentions.
    pub fn locals_mut(&mut self) -> Vec<&mut Local> {
        match self {
            Statement::Assign(l, rvalue) => {
                let mut out = vec![l];
                out.extend(rvalue.locals_mut());
                out
            }
            Statement::Retain(l) | Statement::Release(l) => vec![l],
            Statement::Poll => Vec::new(),
        }
    }
}

impl<'db> Terminator<'db> {
    /// Every local the terminator mentions.
    pub fn locals_mut(&mut self) -> Vec<&mut Local> {
        match self {
            Terminator::Branch { cond: o, .. } | Terminator::Return(o) => {
                o.locals_mut().into_iter().collect()
            }
            Terminator::Switch { place, .. } => vec![&mut place.local],
            Terminator::Call { args, dst, .. } => {
                let mut out: Vec<&mut Local> =
                    args.iter_mut().filter_map(Operand::locals_mut).collect();
                out.push(dst);
                out
            }
            Terminator::TailCall { args, .. } => {
                args.iter_mut().filter_map(Operand::locals_mut).collect()
            }
            Terminator::CallValue {
                callee, args, dst, ..
            } => {
                let mut out: Vec<&mut Local> = callee.locals_mut().into_iter().collect();
                out.extend(args.iter_mut().filter_map(Operand::locals_mut));
                out.push(dst);
                out
            }
            Terminator::TailCallValue { callee, args, .. } => {
                let mut out: Vec<&mut Local> = callee.locals_mut().into_iter().collect();
                out.extend(args.iter_mut().filter_map(Operand::locals_mut));
                out
            }
            Terminator::Jump(_) | Terminator::Trap { .. } => Vec::new(),
        }
    }
}

impl<'db> MirBody<'db> {
    /// The body as text, one statement per line, for tests and debugging.
    pub fn pretty(&self, db: &'db dyn Db) -> String {
        let mut out = String::new();
        for (i, local) in self.locals.iter().enumerate() {
            let kind = if i < self.params { "param" } else { "let" };
            let name = match local.binding {
                Some((_, name)) => format!(" ({})", name.text(db)),
                None => String::new(),
            };
            out += &format!("{kind} _{i}: {}{name}\n", local.ty.display(db));
        }
        for (i, block) in self.blocks.iter().enumerate() {
            out += &format!("bb{i}:\n");
            for statement in &block.statements {
                out += &format!("  {}\n", statement_text(db, statement));
            }
            out += &format!("  {}\n", terminator_text(db, &block.terminator));
        }
        out
    }
}

fn statement_text<'db>(db: &'db dyn Db, statement: &Statement<'db>) -> String {
    match statement {
        Statement::Assign(local, rvalue) => {
            format!("_{} = {}", local.0, rvalue_text(db, rvalue))
        }
        Statement::Retain(local) => format!("retain _{}", local.0),
        Statement::Release(local) => format!("release _{}", local.0),
        Statement::Poll => "poll".into(),
    }
}

fn rvalue_text<'db>(db: &'db dyn Db, rvalue: &Rvalue<'db>) -> String {
    let op = |o: &Operand<'db>| operand_text(db, o);
    let ops = |os: &[Operand<'db>]| os.iter().map(op).collect::<Vec<_>>().join(", ");
    let place = |p: &Place<'db>| place_text(db, p);
    match rvalue {
        Rvalue::Use(o) => op(o),
        Rvalue::Read(p) => place(p),
        Rvalue::Convert(o) => format!("convert {}", op(o)),
        Rvalue::Binary {
            op: bin,
            ty,
            a,
            b,
            check,
        } => {
            let checked = if check.is_some() { "checked " } else { "" };
            format!(
                "{checked}{}.{}({}, {})",
                ty_name(*ty),
                bin_name(*bin),
                op(a),
                op(b)
            )
        }
        Rvalue::Overflows { op: bin, ty, a, b } => format!(
            "overflows {}.{}({}, {})",
            ty_name(*ty),
            bin_name(*bin),
            op(a),
            op(b)
        ),
        Rvalue::FloatOverflow(locals) => format!(
            "overflowed({})",
            locals
                .iter()
                .map(|l| format!("_{}", l.0))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Rvalue::Compare { op: cmp, ty, a, b } => {
            let name = match cmp {
                CmpOp::Eq => "eq",
                CmpOp::Ne => "ne",
                CmpOp::Lt => "lt",
                CmpOp::Le => "le",
                CmpOp::Gt => "gt",
                CmpOp::Ge => "ge",
            };
            format!("{}.{name}({}, {})", ty_name(*ty), op(a), op(b))
        }
        Rvalue::Record { ty, fields } => {
            let fields: Vec<String> = fields
                .iter()
                .map(|(n, o)| format!("{}: {}", n.text(db), op(o)))
                .collect();
            let name = match ty.kind(db) {
                TyKind::Record { .. } => String::new(),
                _ => ty.display(db),
            };
            format!("{name}({})", fields.join(", "))
        }
        Rvalue::List(items) => format!("[{}]", ops(items)),
        Rvalue::Map(entries) if entries.is_empty() => "[:]".into(),
        Rvalue::Map(entries) => format!(
            "[{}]",
            entries
                .iter()
                .map(|(k, v)| format!("{}: {}", op(k), op(v)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Rvalue::Concat(parts) => format!("concat({})", ops(parts)),
        Rvalue::Len(p) => format!("len {}", place(p)),
        Rvalue::Index { list, index } => format!("{}[{}]", place(list), op(index)),
        Rvalue::MapGet { map, key } => format!("get {}[{}]", place(map), op(key)),
        Rvalue::Slice { list, front, back } => {
            format!("slice {}[{front}..-{back}]", place(list))
        }
        Rvalue::Global(item) => format!("value {}", item.name(db).text(db)),
        Rvalue::Closure {
            code,
            captures,
            placement,
            ..
        } => {
            let place = match placement {
                ClosurePlacement::SideStack => "side",
                ClosurePlacement::Heap => "heap",
            };
            format!(
                "closure {} {place}({})",
                func_name(db, *code),
                ops(captures)
            )
        }
        Rvalue::FnValue { code, env } => {
            format!("closure {} with {}", func_name(db, *code), op(env))
        }
    }
}

fn terminator_text<'db>(db: &'db dyn Db, terminator: &Terminator<'db>) -> String {
    let op = |o: &Operand<'db>| operand_text(db, o);
    let ops = |os: &[Operand<'db>]| os.iter().map(op).collect::<Vec<_>>().join(", ");
    match terminator {
        Terminator::Jump(b) => format!("jump bb{}", b.0),
        Terminator::Branch {
            cond,
            then,
            otherwise,
        } => format!("branch {} bb{} bb{}", op(cond), then.0, otherwise.0),
        Terminator::Switch {
            place,
            cases,
            otherwise,
        } => format!(
            "switch {} [{}] else bb{}",
            place_text(db, place),
            cases
                .iter()
                .map(|(t, b)| format!("{}: bb{}", t.display(db), b.0))
                .collect::<Vec<_>>()
                .join(", "),
            otherwise.0
        ),
        Terminator::Call {
            func,
            args,
            dst,
            target,
            ..
        } => format!(
            "_{} = call {}({}) -> bb{}",
            dst.0,
            func_name(db, *func),
            ops(args),
            target.0
        ),
        Terminator::TailCall { func, args, .. } => {
            format!("tail call {}({})", func_name(db, *func), ops(args))
        }
        Terminator::CallValue {
            callee,
            args,
            dst,
            target,
            ..
        } => format!(
            "_{} = call value {}({}) -> bb{}",
            dst.0,
            op(callee),
            ops(args),
            target.0
        ),
        Terminator::TailCallValue { callee, args, .. } => {
            format!("tail call value {}({})", op(callee), ops(args))
        }
        Terminator::Return(o) => format!("return {}", op(o)),
        Terminator::Trap { kind, .. } => {
            let kind = match kind {
                TrapKind::Overflow => "overflow",
                TrapKind::DivideByZero => "divide by zero",
                TrapKind::Index => "index",
                TrapKind::Hole => "hole",
                TrapKind::NoMatch => "no match",
                TrapKind::Error => "error",
                TrapKind::Unsupported => "unsupported",
            };
            format!("trap {kind}")
        }
    }
}

fn func_name<'db>(db: &'db dyn Db, func: InstanceKey<'db>) -> String {
    let owner = match func.owner(db) {
        Owner::Item(item) => item.name(db).text(db).clone(),
        Owner::Test(test) => format!("test {}", test.label(db)),
    };
    match *func.entry(db) {
        Entry::Body => owner,
        Entry::Closure(e) | Entry::Function(e) => format!("{owner}#{}", e.index()),
    }
}

fn operand_text<'db>(db: &'db dyn Db, operand: &Operand<'db>) -> String {
    match operand {
        Operand::Local(l) => format!("_{}", l.0),
        Operand::Const(c) => match c {
            Constant::Int(n) => n.to_string(),
            Constant::Float(bits) => format!("{:?}", f64::from_bits(*bits)),
            Constant::Str(s) => format!("{s:?}"),
            Constant::Bytes(b) => format!("b{:?}", String::from_utf8_lossy(b)),
            Constant::Tag(ty) => ty.display(db),
            Constant::Unit => "()".into(),
        },
    }
}

fn place_text<'db>(db: &'db dyn Db, place: &Place<'db>) -> String {
    let mut text = format!("_{}", place.local.0);
    for step in &place.path {
        match step {
            Step::As(ty) => text = format!("({text} as {})", ty.display(db)),
            Step::Field(name) => text += &format!(".{}", name.text(db)),
            Step::Elem(i) => text += &format!("[{i}]"),
            Step::ElemBack(i) => text += &format!("[-{}]", i + 1),
            Step::Slice { front, back } => text += &format!("[{front}..-{back}]"),
        }
    }
    text
}

fn ty_name(ty: Builtin) -> String {
    match ty {
        Builtin::Fixed(scale) => format!("Fixed[{scale}]"),
        b => b.name().into(),
    }
}

fn bin_name(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "add",
        BinOp::Sub => "sub",
        BinOp::Mul => "mul",
        BinOp::Div => "div",
        BinOp::Rem => "rem",
    }
}
