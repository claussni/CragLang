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

//! The MIR builder (Implementation Plan §11.4.9): a typed body as a
//! control-flow graph in which every operation is explicit.
//!
//! `mir` builds an instance's graph from its HIR and its types, with
//! `case` lowered through a decision tree. Passes then make the rest
//! explicit: the checks of arithmetic, which trap on overflow and on a zero
//! divisor (§3.1.1, §3.1.4), and the reference counts, which follow from a
//! liveness analysis so that a value is released right after its last use.

extern crate crag_db as salsa;

mod build;
mod checks;
mod ir;
mod liveness;

use crag_db::Db;
use crag_hir::{ExprId, Owner, Program};
use crag_types::Ty;

pub use build::place;
pub use checks::insert_overflow_checks;
pub use ir::{
    BinOp, Block, BlockId, ClosurePlacement, CmpOp, Constant, Local, LocalDecl, MirBody, Operand,
    Place, Rvalue, Statement, Terminator, TrapKind,
};
pub use liveness::{Liveness, compute_liveness, insert_drops, insert_rc_ops};

/// A function, test or module-level value with concrete type arguments,
/// or the code of a closure in one: what code is generated for. Until
/// monomorphization (§11.5.10) the arguments are empty.
#[crag_db::interned(debug)]
pub struct InstanceKey<'db> {
    pub owner: Owner<'db>,
    #[returns(ref)]
    pub args: Vec<Ty<'db>>,
    pub entry: Entry,
}

impl<'db> InstanceKey<'db> {
    /// The body of an owner itself.
    pub fn body(db: &'db dyn Db, owner: Owner<'db>) -> InstanceKey<'db> {
        InstanceKey::new(db, owner, Vec::new(), Entry::Body)
    }
}

/// Which code of an owner an instance is (§11.5.9). Every entry but the
/// body is called as a function value: its first parameter is the
/// environment, a box or null.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum Entry {
    Body,
    /// A closure literal or `lazy` expression, or the body of a local
    /// function, by its expression.
    Closure(ExprId),
    /// A declared function used as a value, by the expression that names
    /// it: it calls the function with its arguments, split by the members
    /// of union parameters when the value is lifted (§11.5.5).
    Function(ExprId),
}

impl Entry {
    /// Whether the code takes an environment first.
    pub fn takes_env(self) -> bool {
        self != Entry::Body
    }
}

/// How code is compiled (Compiler Architecture §5). The optimizing and
/// metered tiers arrive with their milestones.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum Tier {
    Baseline,
}

/// The MIR of an instance; none for what has no body, such as a builtin
/// function of the prelude (§19.2) or a type.
#[crag_db::tracked(returns(ref))]
pub fn mir<'db>(
    db: &'db dyn Db,
    program: Program,
    instance: InstanceKey<'db>,
    tier: Tier,
) -> Option<MirBody<'db>> {
    let Tier::Baseline = tier;
    let mut body = build::build(db, program, *instance.owner(db), *instance.entry(db))?;
    insert_overflow_checks(&mut body);
    let live = compute_liveness(&body);
    insert_rc_ops(&mut body, &live);
    insert_drops(&mut body, &live);
    Some(body)
}
