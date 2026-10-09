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

//! The checks of arithmetic made explicit (§3.1.1, §3.1.4): a flag
//! computed before the operation, and a branch to a trap.
//!
//! An integer operation tests whether it overflows; division and remainder
//! test for a zero divisor first. A `Float` has no NaN to produce once
//! divisors are checked, so overflow is its only failure, and a run of
//! consecutive `Float` operations shares one test after the run, before
//! anything stores, passes or compares the results.

use crate::ir::{
    BinOp, Block, BlockId, Constant, Local, LocalDecl, MirBody, Operand, Rvalue, Statement,
    Terminator, TrapKind,
};
use crag_hir::ExprId;
use crag_types::Builtin;

/// A statement, or a test that traps.
enum Item<'db> {
    Statement(Statement<'db>),
    Check {
        flag: Rvalue<'db>,
        kind: TrapKind,
        site: ExprId,
    },
}

pub fn insert_overflow_checks(body: &mut MirBody<'_>) {
    for b in 0..body.blocks.len() {
        let items = items(std::mem::take(&mut body.blocks[b].statements));
        split(body, b, items);
    }
}

/// The statements with their checks.
fn items(statements: Vec<Statement<'_>>) -> Vec<Item<'_>> {
    let mut items = Vec::new();
    let mut run: Vec<Local> = Vec::new();
    let mut last = None;
    let flush = |items: &mut Vec<Item<'_>>, run: &mut Vec<Local>, last: Option<ExprId>| {
        if let (false, Some(site)) = (run.is_empty(), last) {
            items.push(Item::Check {
                flag: Rvalue::FloatOverflow(std::mem::take(run)),
                kind: TrapKind::Overflow,
                site,
            });
        }
    };
    for statement in statements {
        let Statement::Assign(
            dst,
            Rvalue::Binary {
                op,
                ty,
                a,
                b,
                check: Some(site),
            },
        ) = statement
        else {
            flush(&mut items, &mut run, last);
            items.push(Item::Statement(statement));
            continue;
        };
        let zero = match ty {
            Builtin::Float => Constant::Float(0.0f64.to_bits()),
            _ => Constant::Int(0),
        };
        let divides = matches!(op, BinOp::Div | BinOp::Rem);
        if ty != Builtin::Float || divides {
            flush(&mut items, &mut run, last);
        }
        if divides {
            items.push(Item::Check {
                flag: Rvalue::Compare {
                    op: crate::ir::CmpOp::Eq,
                    ty,
                    a: b.clone(),
                    b: Operand::Const(zero),
                },
                kind: TrapKind::DivideByZero,
                site,
            });
        }
        let signed = ty.int_range().is_some_and(|(least, _)| least < 0);
        let overflows = match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul => true,
            BinOp::Div => signed || matches!(ty, Builtin::Fixed(_)),
            // The remainder is never larger than the divisor.
            BinOp::Rem => false,
        };
        if overflows && ty != Builtin::Float {
            items.push(Item::Check {
                flag: Rvalue::Overflows {
                    op,
                    ty,
                    a: a.clone(),
                    b: b.clone(),
                },
                kind: TrapKind::Overflow,
                site,
            });
        }
        items.push(Item::Statement(Statement::Assign(
            dst,
            Rvalue::Binary {
                op,
                ty,
                a,
                b,
                check: None,
            },
        )));
        if ty == Builtin::Float && op != BinOp::Rem {
            run.push(dst);
            last = Some(site);
        }
    }
    flush(&mut items, &mut run, last);
    items
}

/// Puts the items back into the block, ending it at each check with a
/// branch to a trap of its own and continuing in a new block.
fn split<'db>(body: &mut MirBody<'db>, b: usize, items: Vec<Item<'db>>) {
    let terminator = std::mem::replace(
        &mut body.blocks[b].terminator,
        Terminator::Trap {
            kind: TrapKind::Error,
            site: None,
        },
    );
    let mut current = b;
    let mut statements = Vec::new();
    for item in items {
        match item {
            Item::Statement(s) => statements.push(s),
            Item::Check { flag, kind, site } => {
                let local = Local(body.locals.len() as u32);
                body.locals.push(LocalDecl {
                    ty: body.bool_ty,
                    binding: None,
                    counted: false,
                });
                statements.push(Statement::Assign(local, flag));
                let trap = push(
                    body,
                    Terminator::Trap {
                        kind,
                        site: Some(site),
                    },
                );
                let next = push(
                    body,
                    Terminator::Trap {
                        kind: TrapKind::Error,
                        site: None,
                    },
                );
                body.blocks[current] = Block {
                    statements: std::mem::take(&mut statements),
                    terminator: Terminator::Branch {
                        cond: Operand::Local(local),
                        then: trap,
                        otherwise: next,
                    },
                };
                current = next.index();
            }
        }
    }
    body.blocks[current] = Block {
        statements,
        terminator,
    };
}

fn push<'db>(body: &mut MirBody<'db>, terminator: Terminator<'db>) -> BlockId {
    body.blocks.push(Block {
        statements: Vec::new(),
        terminator,
    });
    BlockId(body.blocks.len() as u32 - 1)
}
