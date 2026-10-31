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

//! The inliner (Implementation Plan §11.10.1): in the optimizing tier, a
//! direct call of a small function is replaced by a copy of the function's
//! code, before the reference counts are placed, so that they follow the
//! values through the copy as through the caller's own code.
//!
//! The copied blocks name the call in `MirBody::inlined`, so that their
//! sites, expressions of the callee, are found in the callee's module, and
//! a trap in them reports the callee as a frame of its own, marked as
//! inlined. A parameter the callee never assigns becomes the caller's
//! local it is given, so that a value the caller lends is still only read.
//!
//! Calls reach a function through its slot, which a reload refills. A
//! guard therefore runs the copy only while the slot holds the code loaded
//! with the caller's, and makes the call otherwise, so that a frame that
//! runs on through a reload reaches the new code as a call would.
//!
//! Code that keeps state in its frame is left as a call: closures on the
//! side stack, which a loop around the call would let pile up, trap
//! handlers, transactions, scopes, signal blocks and the positions tests
//! report. So is a callee among the functions whose code a block is
//! already, which bounds recursion.
//!
//! A call of a function value that is known to be a small closure, made in
//! the body from captured values that do not change after, is specialized
//! the same way: its code is copied in place of the call, and its reads of
//! the environment read the captured values themselves; a function value
//! of the closure's own code is the closure called. The guard's fallback
//! makes the closure again, on the heap, and calls it, so that a closure
//! the copies leave unused is not made at all.

use std::collections::HashSet;

use crag_db::Db;
use crag_hir::{ExprId, ItemKind, Name, Owner, Program, c_function};
use crag_types::{Step, Ty, TyKind, fields_of};

use crate::borrow::assigned;
use crate::ir::{
    Block, BlockId, ClosurePlacement, Inlined, Intrinsic, Local, LocalDecl, MirBody, Operand,
    Place, Rvalue, Statement, Terminator, TrapKind,
};
use crate::{Entry, InstanceKey, built};

/// The size of code by the inliner's measure: a unit for each statement
/// but steps, and for each block's terminator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct InlineCost(pub usize);

impl InlineCost {
    /// The largest callee copied in place of a call.
    pub const CALLEE: InlineCost = InlineCost(24);
    /// The size beyond which a body copies in no more callees.
    pub const BODY: InlineCost = InlineCost(1500);

    pub fn of(body: &MirBody<'_>) -> InlineCost {
        let units = body.blocks.iter().map(|block| {
            let statements = block.statements.iter();
            1 + statements
                .filter(|s| !matches!(s, Statement::Step { .. }))
                .count()
        });
        InlineCost(units.sum())
    }
}

/// How deep inlined calls nest; less than 16, which the debugger counts
/// on to tell code inlined into a frame from the frames below it.
const DEPTH: usize = 4;

/// Replaces the calls of the body that `should_inline` picks by their
/// callees' code, and the calls of the closures `known_closure` finds by
/// theirs, then the calls in that code in turn. Closures left unused go.
pub(crate) fn inline_calls<'db>(
    db: &'db dyn Db,
    program: Program,
    instance: InstanceKey<'db>,
    body: &mut MirBody<'db>,
) {
    let mut size = InlineCost::of(body);
    // The calls a guard falls back to stay calls.
    let mut fallbacks = HashSet::new();
    let mut specialized = false;
    // Blocks the copies add come after, and are looked at in turn.
    let mut b = 0;
    while b < body.blocks.len() {
        if fallbacks.contains(&b) {
        } else if let Some(callee) = should_inline(db, program, instance, body, b, size) {
            size.0 += InlineCost::of(callee).0;
            fallbacks.insert(inline_call(body, b, callee).index());
        } else if let Some(closure) = known_closure(db, program, instance, body, b, size) {
            size.0 += InlineCost::of(closure.code).0;
            fallbacks.insert(specialize_closure_call(body, b, &closure).index());
            specialized = true;
        }
        b += 1;
    }
    if specialized {
        remove_unused_closures(db, body);
    }
}

/// The callee's code, if the call that ends the block is to be replaced
/// by it: a small function's body, whose code keeps no state in its frame,
/// that the block's code is not already part of.
pub fn should_inline<'db>(
    db: &'db dyn Db,
    program: Program,
    instance: InstanceKey<'db>,
    body: &MirBody<'db>,
    b: usize,
    size: InlineCost,
) -> Option<&'db MirBody<'db>> {
    let (func, args, result) = match &body.blocks[b].terminator {
        Terminator::Call {
            func, args, dst, ..
        } => (func, args, body.locals[dst.index()].ty),
        Terminator::TailCall { func, args, .. } => (func, args, body.result),
        _ => return None,
    };
    let Owner::Item(item) = *func.owner(db) else {
        return None;
    };
    if *func.entry(db) != Entry::Body
        || *item.kind(db) != ItemKind::Function
        || c_function(db, item).is_some()
    {
        return None;
    }
    let chain = enclosing(body, body.blocks[b].inlined);
    if *func == instance || chain.len() >= DEPTH || chain.contains(func) {
        return None;
    }
    let callee = built(db, program, *func).as_ref()?;
    if callee.env || result != callee.result || !small(callee, size) {
        return None;
    }
    // The arguments are of the parameters' types, as the callee's code
    // expects its locals.
    let typed = args.iter().enumerate().all(|(i, arg)| match arg {
        Operand::Local(l) => body.locals[l.index()].ty == callee.locals[i].ty,
        Operand::Const(_) => true,
    });
    typed.then_some(callee)
}

/// Whether code is copied in place of a call in a body of `size`: small,
/// with all of it lowered, and keeping no state in its frame.
fn small(callee: &MirBody<'_>, size: InlineCost) -> bool {
    let cost = InlineCost::of(callee);
    callee.unsupported.is_empty()
        && cost <= InlineCost::CALLEE
        && size.0 + cost.0 <= InlineCost::BODY.0
        && keeps_no_state(callee)
}

/// A function value a call is known to call: a closure the body makes, of
/// code with an environment.
pub struct KnownClosure<'a, 'db> {
    pub func: InstanceKey<'db>,
    pub code: &'a MirBody<'db>,
    /// The local the call takes the value from.
    pub value: Local,
    pub env: ClosureEnv<'db>,
}

/// Where a known closure's environment comes from.
pub enum ClosureEnv<'db> {
    /// A closure literal's captured values, by the environment's fields.
    Captures {
        ty: Ty<'db>,
        fields: Vec<(Name<'db>, Operand<'db>)>,
    },
    /// A local function naming itself, with an environment it has.
    Value(Local),
}

/// The closure the function value that the call ending block `b` calls
/// is, if its code is to be copied in place of the call: small code, as
/// `should_inline` asks of a function's, called with arguments of its
/// parameters' types, whose environment's values do not change between
/// the closure's making and the call, since each is assigned once at most.
pub fn known_closure<'db>(
    db: &'db dyn Db,
    program: Program,
    instance: InstanceKey<'db>,
    body: &MirBody<'db>,
    b: usize,
    size: InlineCost,
) -> Option<KnownClosure<'db, 'db>> {
    let (callee, args, result) = match &body.blocks[b].terminator {
        Terminator::CallValue {
            callee, args, dst, ..
        } => (callee, args, body.locals[dst.index()].ty),
        Terminator::TailCallValue { callee, args, .. } => (callee, args, body.result),
        _ => return None,
    };
    let Operand::Local(value) = *callee else {
        return None;
    };
    let once = |l: Local| definitions(body, l) <= usize::from(l.index() >= body.params);
    // Through the copies of the value, to where it is made.
    let mut at = value;
    let made = loop {
        if definitions(body, at) != 1 {
            return None;
        }
        match definition(body, at)? {
            Rvalue::Use(Operand::Local(from)) | Rvalue::Convert(Operand::Local(from)) => at = *from,
            Rvalue::Read(Place { local: from, path }) if path.is_empty() => at = *from,
            made => break made,
        }
    };
    let (func, env) = match made {
        Rvalue::Closure {
            code,
            env,
            captures,
            ..
        } => {
            let names = fields_of(db, program, *env)?;
            if names.len() != captures.len() {
                return None;
            }
            let mut fields = Vec::new();
            for ((name, ty), op) in names.into_iter().zip(captures) {
                if let Operand::Local(c) = op
                    && (!once(*c) || body.locals[c.index()].ty != ty)
                {
                    return None;
                }
                fields.push((name, op.clone()));
            }
            (*code, ClosureEnv::Captures { ty: *env, fields })
        }
        Rvalue::FnValue {
            code,
            env: Operand::Local(e),
        } if once(*e) => (*code, ClosureEnv::Value(*e)),
        _ => return None,
    };
    let chain = enclosing(body, body.blocks[b].inlined);
    if func == instance || chain.len() >= DEPTH || chain.contains(&func) {
        return None;
    }
    let code = built(db, program, func).as_ref()?;
    if !code.env
        || code.params != args.len() + 1
        || result != code.result
        || !small(code, size)
        || assigned(code, Local(0))
    {
        return None;
    }
    let typed = args.iter().enumerate().all(|(i, arg)| match arg {
        Operand::Local(l) => body.locals[l.index()].ty == code.locals[i + 1].ty,
        Operand::Const(_) => true,
    });
    let env_read = match &env {
        ClosureEnv::Captures { fields, .. } => {
            reads_env(code, func, fields, body.locals[value.index()].ty)
        }
        ClosureEnv::Value(_) => true,
    };
    (typed && env_read).then_some(KnownClosure {
        func,
        code,
        value,
        env,
    })
}

/// How many times the body assigns the local.
fn definitions(body: &MirBody<'_>, local: Local) -> usize {
    body.blocks
        .iter()
        .map(|block| {
            let assigns = block
                .statements
                .iter()
                .filter(|s| matches!(s, Statement::Assign(dst, _) if *dst == local))
                .count();
            let calls = matches!(
                block.terminator,
                Terminator::Call { dst, .. } | Terminator::CallValue { dst, .. } if dst == local
            );
            assigns + usize::from(calls)
        })
        .sum()
}

/// The rvalue of the statement that assigns the local, if one does.
fn definition<'a, 'db>(body: &'a MirBody<'db>, local: Local) -> Option<&'a Rvalue<'db>> {
    body.blocks.iter().find_map(|block| {
        block.statements.iter().find_map(|s| match s {
            Statement::Assign(dst, rvalue) if *dst == local => Some(rvalue),
            _ => None,
        })
    })
}

/// Whether closure code uses its environment only to read the captured
/// values, as they are or a part of them, and to name itself as a value
/// of the closure's type, `value_ty`.
fn reads_env<'db>(
    code: &MirBody<'db>,
    func: InstanceKey<'db>,
    fields: &[(Name<'db>, Operand<'db>)],
    value_ty: Ty<'db>,
) -> bool {
    let env = Local(0);
    let mentions = |s: &Statement<'db>| s.clone().locals_mut().into_iter().any(|l| *l == env);
    code.blocks.iter().all(|block| {
        let statements = block.statements.iter().all(|s| match s {
            Statement::Assign(dst, rvalue) if *dst != env => match rvalue {
                Rvalue::Read(Place { local, path }) if *local == env => match path.first() {
                    Some(Step::Field(name)) => fields.iter().any(|(n, op)| {
                        n == name && (matches!(op, Operand::Local(_)) || path.len() == 1)
                    }),
                    _ => false,
                },
                Rvalue::FnValue {
                    code: c,
                    env: Operand::Local(e),
                } if *e == env => *c == func && code.locals[dst.index()].ty == value_ty,
                _ => !mentions(s),
            },
            Statement::Step { .. } => true,
            _ => !mentions(s),
        });
        statements
            && !block
                .terminator
                .clone()
                .locals_mut()
                .into_iter()
                .any(|l| *l == env)
    })
}

/// Replaces the call of a function value that ends block `b` by a copy
/// of the code of the closure it is known to be, as `inline_call` does
/// for a call of a function, and returns the guard's fallback, which makes
/// the closure again and calls it.
pub fn specialize_closure_call<'db>(
    body: &mut MirBody<'db>,
    b: usize,
    closure: &KnownClosure<'_, 'db>,
) -> BlockId {
    let fallback = BlockId(body.blocks.len() as u32);
    let value_ty = body.locals[closure.value.index()].ty;
    let again = Local(body.locals.len() as u32);
    body.locals.push(LocalDecl {
        ty: value_ty,
        binding: None,
        counted: true,
        split: false,
        borrowed: false,
    });
    let make = match &closure.env {
        ClosureEnv::Captures { ty, fields } => Rvalue::Closure {
            code: closure.func,
            env: *ty,
            captures: fields.iter().map(|(_, op)| op.clone()).collect(),
            placement: ClosurePlacement::Heap,
        },
        ClosureEnv::Value(e) => Rvalue::FnValue {
            code: closure.func,
            env: Operand::Local(*e),
        },
    };
    let mut call = body.blocks[b].terminator.clone();
    if let Terminator::CallValue { callee, .. } | Terminator::TailCallValue { callee, .. } =
        &mut call
    {
        *callee = Operand::Local(again);
    }
    body.blocks.push(Block {
        statements: vec![Statement::Assign(again, make)],
        terminator: call.clone(),
        catch: body.blocks[b].catch,
        inlined: body.blocks[b].inlined,
    });
    let (args, site, exit, unwind, catch) = match call {
        Terminator::CallValue {
            args,
            dst,
            target,
            site,
            unwind,
            catch,
            ..
        } => (args, site, Some((dst, target)), unwind, catch),
        Terminator::TailCallValue { args, site, .. } => (args, site, None, None, None),
        _ => unreachable!("a call of a function value is specialized"),
    };
    let (env, params) = match &closure.env {
        ClosureEnv::Captures { fields, .. } => (Some((fields.as_slice(), closure.value)), {
            // The environment's local stands for no value of the caller.
            std::iter::once(Operand::Const(crate::ir::Constant::Unit))
                .chain(args)
                .collect()
        }),
        ClosureEnv::Value(e) => (
            None,
            std::iter::once(Operand::Local(*e)).chain(args).collect(),
        ),
    };
    let copy = Copy {
        func: closure.func,
        site,
        params,
        env,
        exit,
        unwind,
        catch,
    };
    copy_in(body, b, fallback, closure.code, copy);
    fallback
}

/// Removes what makes function values that nothing uses: closures, and
/// their copies, which the specialized calls left. Steps no longer show
/// them.
fn remove_unused_closures<'db>(db: &'db dyn Db, body: &mut MirBody<'db>) {
    let mut removed = HashSet::new();
    loop {
        let mut used = vec![false; body.locals.len()];
        for block in &mut body.blocks {
            for s in &mut block.statements {
                match s {
                    Statement::Assign(_, rvalue) => {
                        for l in rvalue.locals_mut() {
                            used[l.index()] = true;
                        }
                    }
                    Statement::Step { .. } => {}
                    _ => {
                        for l in s.locals_mut() {
                            used[l.index()] = true;
                        }
                    }
                }
            }
            for l in block.terminator.locals_mut() {
                used[l.index()] = true;
            }
        }
        let mut changed = false;
        for block in &mut body.blocks {
            block.statements.retain(|s| {
                let Statement::Assign(dst, rvalue) = s else {
                    return true;
                };
                let function = matches!(body.locals[dst.index()].ty.kind(db), TyKind::Fn { .. });
                let made = match rvalue {
                    Rvalue::Closure { .. } | Rvalue::FnValue { .. } => true,
                    Rvalue::Use(Operand::Local(_)) | Rvalue::Convert(Operand::Local(_)) => function,
                    Rvalue::Read(Place { path, .. }) => function && path.is_empty(),
                    _ => false,
                };
                let dead = made && !used[dst.index()] && dst.index() >= body.params;
                if dead {
                    removed.insert(*dst);
                    changed = true;
                }
                !dead
            });
        }
        if !changed {
            break;
        }
    }
    for block in &mut body.blocks {
        for s in &mut block.statements {
            if let Statement::Step { locals, .. } = s {
                locals.retain(|l| !removed.contains(l));
            }
        }
    }
}

/// The functions whose code an inlined call's blocks are, innermost first.
fn enclosing<'db>(body: &MirBody<'db>, mut inlined: Option<u32>) -> Vec<InstanceKey<'db>> {
    let mut out = Vec::new();
    while let Some(k) = inlined {
        let call = &body.inlined[k as usize];
        out.push(call.func);
        inlined = call.parent;
    }
    out
}

/// Whether the code keeps nothing in its frame that its caller's frame
/// would keep differently.
fn keeps_no_state(body: &MirBody<'_>) -> bool {
    body.blocks.iter().all(|block| {
        let statements = block.statements.iter().all(|s| match s {
            Statement::Assign(
                _,
                Rvalue::Closure {
                    placement: ClosurePlacement::SideStack,
                    ..
                },
            ) => false,
            Statement::Assign(_, Rvalue::Intrinsic(intrinsic, _)) => !matches!(
                intrinsic,
                Intrinsic::TxBegin
                    | Intrinsic::TxDepth
                    | Intrinsic::TxUnwind
                    | Intrinsic::TxCommit
                    | Intrinsic::TxAbort
                    | Intrinsic::TxRetry
                    | Intrinsic::TxThrow
                    | Intrinsic::TxConflicted
                    | Intrinsic::TrapCaught(_)
                    | Intrinsic::TrapCaughtText(_)
                    | Intrinsic::SidePtr
                    | Intrinsic::SideEnd
                    | Intrinsic::SideReset
                    | Intrinsic::ScopeNew
                    | Intrinsic::ScopeStart
                    | Intrinsic::ScopeNext
                    | Intrinsic::ScopeResult
                    | Intrinsic::ScopeCancel
                    | Intrinsic::ScopeEnd
                    | Intrinsic::SignalDrain
                    | Intrinsic::SignalMark
                    | Intrinsic::SignalOn
                    | Intrinsic::SignalReset
                    | Intrinsic::TestFailure
                    | Intrinsic::Site(_)
            ),
            _ => true,
        });
        let terminator = match &block.terminator {
            Terminator::Call { unwind, catch, .. }
            | Terminator::CallValue { unwind, catch, .. } => unwind.is_none() && catch.is_none(),
            Terminator::Trap { kind, catch, .. } => catch.is_none() && *kind != TrapKind::Rethrow,
            _ => true,
        };
        block.catch.is_none() && statements && terminator
    })
}

/// Replaces the call that ends block `b` by a copy of the callee's code,
/// whose returns give the call's result and go on where the call did. A
/// trap in the copy goes to the trap handler around the call, and a
/// transaction it leaves to the call's handler, as from the callee's frame.
/// The copy of a tail call returns, and makes tail calls, as the callee.
///
/// A guard goes to the copy while the callee's slot holds the code loaded
/// with the function, else to the call, in a block of its own, which this
/// returns.
pub fn inline_call<'db>(body: &mut MirBody<'db>, b: usize, callee: &MirBody<'db>) -> BlockId {
    let fallback = BlockId(body.blocks.len() as u32);
    let call = body.blocks[b].terminator.clone();
    body.blocks.push(Block {
        statements: Vec::new(),
        terminator: call.clone(),
        catch: body.blocks[b].catch,
        inlined: body.blocks[b].inlined,
    });
    // Where the copy's returns go, the call's result and block, and the
    // call's handlers; a tail call has none.
    let copy = match call {
        Terminator::Call {
            func,
            args,
            dst,
            target,
            site,
            unwind,
            catch,
        } => Copy {
            func,
            site,
            params: args,
            env: None,
            exit: Some((dst, target)),
            unwind,
            catch,
        },
        Terminator::TailCall { func, args, site } => Copy {
            func,
            site,
            params: args,
            env: None,
            exit: None,
            unwind: None,
            catch: None,
        },
        _ => unreachable!("a call is inlined"),
    };
    copy_in(body, b, fallback, callee, copy);
    fallback
}

/// A call whose callee's code is copied in its place.
struct Copy<'e, 'db> {
    func: InstanceKey<'db>,
    site: ExprId,
    /// The values of the callee's parameters.
    params: Vec<Operand<'db>>,
    /// The captured values a closure's environment, its local 0, holds by
    /// field, and the closure, which it names itself as.
    env: Option<(&'e [(Name<'db>, Operand<'db>)], Local)>,
    exit: Option<(Local, BlockId)>,
    unwind: Option<BlockId>,
    catch: Option<BlockId>,
}

/// Puts a guard at the end of block `b` that goes to a copy of the
/// callee's code or to `fallback`, and makes the copy.
fn copy_in<'db>(
    body: &mut MirBody<'db>,
    b: usize,
    fallback: BlockId,
    callee: &MirBody<'db>,
    copy: Copy<'_, 'db>,
) {
    let Copy {
        func,
        site,
        params: args,
        env,
        exit,
        unwind,
        catch,
    } = copy;
    let entry_block = BlockId(body.blocks.len() as u32);
    body.blocks[b].terminator = Terminator::Guard {
        func,
        inlined: entry_block,
        fallback,
    };
    let k = body.inlined.len() as u32;
    body.inlined.push(Inlined {
        func,
        site,
        parent: body.blocks[b].inlined,
    });
    // A parameter the callee never assigns is the local given for it;
    // others are locals of their own, which take the arguments.
    let mut map = Vec::with_capacity(callee.locals.len());
    let mut entry = Vec::new();
    // A closure's environment is read from what it captured.
    let unmapped = Local(u32::MAX);
    for (i, decl) in callee.locals.iter().enumerate() {
        if i == 0 && env.is_some() {
            map.push(unmapped);
            continue;
        }
        if i < callee.params
            && let Operand::Local(l) = args[i]
            && !assigned(callee, Local(i as u32))
        {
            map.push(l);
            continue;
        }
        let local = Local(body.locals.len() as u32);
        body.locals.push(LocalDecl {
            borrowed: false,
            ..decl.clone()
        });
        map.push(local);
        if i < callee.params {
            entry.push(Statement::Assign(local, Rvalue::Use(args[i].clone())));
        }
    }
    let base = body.blocks.len() as u32;
    for (i, block) in callee.blocks.iter().enumerate() {
        let mut block = block.clone();
        for s in &mut block.statements {
            for l in s.locals_mut() {
                *l = map[l.index()];
            }
            if let Some((fields, value)) = env {
                read_captures(s, unmapped, fields, value);
            }
        }
        // The callee's entry is no branch target, so its parameters are
        // given once.
        if i == 0 {
            block.statements.splice(0..0, entry.drain(..));
        }
        for l in block.terminator.locals_mut() {
            *l = map[l.index()];
        }
        for s in block.terminator.successors_mut() {
            s.0 += base;
        }
        block.terminator = match (block.terminator, exit) {
            (Terminator::Return(op), Some((dst, target))) => {
                block
                    .statements
                    .push(Statement::Assign(dst, Rvalue::Use(op)));
                Terminator::Jump(target)
            }
            (Terminator::TailCall { func, args, site }, Some((dst, target))) => Terminator::Call {
                func,
                args,
                dst,
                target,
                site,
                unwind,
                catch,
            },
            (Terminator::TailCallValue { callee, args, site }, Some((dst, target))) => {
                Terminator::CallValue {
                    callee,
                    args,
                    dst,
                    target,
                    site,
                    unwind,
                    catch,
                }
            }
            (
                Terminator::Call {
                    func,
                    args,
                    dst,
                    target,
                    site,
                    ..
                },
                _,
            ) => Terminator::Call {
                func,
                args,
                dst,
                target,
                site,
                unwind,
                catch,
            },
            (
                Terminator::CallValue {
                    callee,
                    args,
                    dst,
                    target,
                    site,
                    ..
                },
                _,
            ) => Terminator::CallValue {
                callee,
                args,
                dst,
                target,
                site,
                unwind,
                catch,
            },
            (
                Terminator::Trap {
                    kind, site, detail, ..
                },
                _,
            ) => Terminator::Trap {
                kind,
                site,
                detail,
                catch,
            },
            (other, _) => other,
        };
        body.blocks.push(Block {
            statements: block.statements,
            terminator: block.terminator,
            catch,
            inlined: Some(k),
        });
    }
}

/// Reads what a statement of a closure's code reads from its environment,
/// `env`, from the captured values instead, and names the closure `value`
/// where the code names itself.
fn read_captures<'db>(
    statement: &mut Statement<'db>,
    env: Local,
    fields: &[(Name<'db>, Operand<'db>)],
    value: Local,
) {
    match statement {
        Statement::Assign(_, rvalue @ Rvalue::Read(_)) => {
            let Rvalue::Read(Place { local, path }) = rvalue else {
                return;
            };
            let (true, Some(Step::Field(name))) = (*local == env, path.first()) else {
                return;
            };
            let (_, op) = fields
                .iter()
                .find(|(n, _)| n == name)
                .expect("a captured value");
            *rvalue = match op {
                Operand::Local(c) => Rvalue::Read(Place {
                    local: *c,
                    path: path[1..].to_vec(),
                }),
                Operand::Const(_) => Rvalue::Use(op.clone()),
            };
        }
        Statement::Assign(_, rvalue @ Rvalue::FnValue { .. }) => {
            if matches!(rvalue, Rvalue::FnValue { env: Operand::Local(e), .. } if *e == env) {
                *rvalue = Rvalue::Read(Place::local(value));
            }
        }
        Statement::Step { locals, .. } => locals.retain(|&l| l != env),
        _ => {}
    }
}
