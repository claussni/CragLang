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

use std::collections::HashSet;

use crag_db::Db;
use crag_hir::{ItemKind, Owner, Program, c_function};

use crate::borrow::assigned;
use crate::ir::{
    Block, BlockId, ClosurePlacement, Inlined, Intrinsic, Local, LocalDecl, MirBody, Operand,
    Rvalue, Statement, Terminator, TrapKind,
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
/// callees' code, and the calls in that code in turn.
pub(crate) fn inline_calls<'db>(
    db: &'db dyn Db,
    program: Program,
    instance: InstanceKey<'db>,
    body: &mut MirBody<'db>,
) {
    let mut size = InlineCost::of(body);
    // The calls a guard falls back to stay calls.
    let mut fallbacks = HashSet::new();
    // Blocks the copies add come after, and are looked at in turn.
    let mut b = 0;
    while b < body.blocks.len() {
        if !fallbacks.contains(&b)
            && let Some(callee) = should_inline(db, program, instance, body, b, size)
        {
            size.0 += InlineCost::of(callee).0;
            fallbacks.insert(inline_call(body, b, callee).index());
        }
        b += 1;
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
    let cost = InlineCost::of(callee);
    if callee.env
        || !callee.unsupported.is_empty()
        || cost > InlineCost::CALLEE
        || size.0 + cost.0 > InlineCost::BODY.0
        || result != callee.result
        || !keeps_no_state(callee)
    {
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
    let entry_block = BlockId(fallback.0 + 1);
    let call = body.blocks[b].terminator.clone();
    body.blocks.push(Block {
        statements: Vec::new(),
        terminator: call.clone(),
        catch: body.blocks[b].catch,
        inlined: body.blocks[b].inlined,
    });
    // Where the copy's returns go, the call's result and block, and the
    // call's handlers; a tail call has none.
    let (func, args, site, exit, unwind, catch) = match call {
        Terminator::Call {
            func,
            args,
            dst,
            target,
            site,
            unwind,
            catch,
        } => (func, args, site, Some((dst, target)), unwind, catch),
        Terminator::TailCall { func, args, site } => (func, args, site, None, None, None),
        _ => unreachable!("a call is inlined"),
    };
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
    for (i, decl) in callee.locals.iter().enumerate() {
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
    fallback
}
