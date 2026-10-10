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

//! Tail calls and the side stack (Implementation Plan §11.5.11).
//!
//! A tail call pops the caller's part of the side stack before it jumps,
//! so a closure whose environment is there cannot go along: neither as an
//! argument nor as the function value called. Its environment would have
//! no owner in the callee's frame, a tail-recursive loop would grow the
//! side stack by one environment per round, and the locals it borrows die
//! with the caller. Such a closure is placed on the heap instead, with
//! every side-stack closure it captures, so its environment holds its own
//! references and is released like any box.

use crate::ir::{ClosurePlacement, MirBody, Operand, Rvalue, Statement, Terminator};

/// Where a closure is made: a block and a statement in it.
type Site = (usize, usize);

/// Places on the heap every side-stack closure that a tail call passes or
/// calls, directly or captured by one that does.
pub fn place_tail_closures(body: &mut MirBody<'_>) {
    let origins = origins(body);
    let mut pending: Vec<Site> = Vec::new();
    for block in &body.blocks {
        let operands = match &block.terminator {
            Terminator::TailCall { args, .. } => args.iter().collect::<Vec<_>>(),
            Terminator::TailCallValue { callee, args, .. } => {
                std::iter::once(callee).chain(args).collect()
            }
            _ => continue,
        };
        for op in operands {
            if let Operand::Local(l) = op {
                pending.extend(origins[l.index()].iter().copied());
            }
        }
    }
    while let Some((b, s)) = pending.pop() {
        let Statement::Assign(
            _,
            Rvalue::Closure {
                placement,
                captures,
                ..
            },
        ) = &mut body.blocks[b].statements[s]
        else {
            unreachable!("an origin is a closure");
        };
        if *placement == ClosurePlacement::Heap {
            continue;
        }
        *placement = ClosurePlacement::Heap;
        // A heap environment outlives the frame, so what it captures from
        // the side stack must too.
        for c in captures.iter() {
            if let Operand::Local(l) = c {
                pending.extend(origins[l.index()].iter().copied());
            }
        }
    }
}

/// The side-stack closures with an environment that each local may hold:
/// those assigned to it and those of the locals copied into it.
fn origins(body: &MirBody<'_>) -> Vec<Vec<Site>> {
    let mut origins: Vec<Vec<Site>> = vec![Vec::new(); body.locals.len()];
    loop {
        let mut changed = false;
        for (b, block) in body.blocks.iter().enumerate() {
            for (s, statement) in block.statements.iter().enumerate() {
                let Statement::Assign(dst, rvalue) = statement else {
                    continue;
                };
                let add = match rvalue {
                    Rvalue::Closure {
                        captures,
                        placement: ClosurePlacement::SideStack,
                        ..
                    } if !captures.is_empty() => vec![(b, s)],
                    Rvalue::Use(Operand::Local(src)) | Rvalue::Convert(Operand::Local(src)) => {
                        origins[src.index()].clone()
                    }
                    _ => continue,
                };
                for site in add {
                    if !origins[dst.index()].contains(&site) {
                        origins[dst.index()].push(site);
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            return origins;
        }
    }
}
