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

//! Code generation (Implementation Plan §11.4.10): MIR translated into the
//! facade's LIR and compiled by Cranelift into a code object per instance.
//!
//! Values are laid out in words as Compiler Architecture §11 describes;
//! `layout` decides how. Boxes are allocated and counted inline, the runtime
//! frees them using the descriptors of their types, lists and maps grow and
//! are read through calls of the runtime, and checks trap through a call of
//! the runtime. Every call is a safepoint whose stack map lists
//! the boxes the frame holds.
//!
//! Baseline code calls other Crag functions through their slots
//! (Implementation Plan §11.6.4), so that an image can replace a function
//! without reloading its callers. A slot is the function's id and its
//! signature: the index of the function type its MIR has, parameters and
//! result, which stays the same while the signature does.
//!
//! A read of a module-level value calls the code that computes it. That
//! code keeps the value in a cell the loader makes, and gives what the cell
//! holds once it is full (Implementation Plan §11.6.2).

extern crate crag_db as salsa;

mod layout;
mod lower;

use std::sync::OnceLock;

use crag_abi::{SlotKey, TypeDescriptor};

use crag_codegen::{CodeObject, CodegenSettings, OptLevel, Target, compile, target_for};
use crag_db::Db;
use crag_db::plumbing::AsId;
use crag_hir::{ItemKind, Owner, Program};
use crag_mir::{Entry, InstanceKey, Tier, mir};
use crag_types::{Ty, TyKind};

pub use layout::{
    FieldSlot, Layout, element_layout, layout, record_layout, type_descriptor, type_index,
};
pub use lower::{Lowered, func_id, lower_to_lir};

/// The code of an instance, ready for the loader.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Code<'db> {
    pub object: CodeObject,
    /// The function the object is loaded as, and the slot it fills, which
    /// calls name.
    pub func: crag_codegen::FuncId,
    pub slot: SlotKey,
    /// Words of parameters and results, for the entry stub.
    pub params: u32,
    pub returns: u32,
    /// The instances it calls, which must be loaded with it.
    pub calls: Vec<InstanceKey<'db>>,
    /// The types of the boxes it allocates or whose elements it reads, by
    /// type index, whose descriptors the image must hold.
    pub types: Vec<(u32, TypeDescriptor)>,
    /// What it could not compile; each traps where it is reached.
    pub unsupported: Vec<&'static str>,
}

/// The target code is generated for: the host's.
fn host() -> &'static Target {
    static HOST: OnceLock<Target> = OnceLock::new();
    HOST.get_or_init(|| target_for("x86_64-unknown-linux-gnu").expect("the host is supported"))
}

/// The slot of an instance: its function id and its signature.
pub fn slot_key<'db>(db: &'db dyn Db, program: Program, instance: InstanceKey<'db>) -> SlotKey {
    SlotKey {
        func: func_id(instance),
        signature: *slot_signature(db, program, instance),
    }
}

/// The signature part of an instance's slot: the index of the function
/// type of its MIR, or zero for what has none. A query of its own, so that
/// callers depend on the signature and not on the body.
#[crag_db::tracked]
fn slot_signature<'db>(db: &'db dyn Db, program: Program, instance: InstanceKey<'db>) -> u32 {
    let Some(body) = mir(db, program, instance, Tier::Baseline) else {
        return 0;
    };
    let ty = Ty::new(
        db,
        TyKind::Fn {
            params: body.locals[..body.params].iter().map(|l| l.ty).collect(),
            result: body.result,
            pure: false,
        },
    );
    ty.as_id().index()
}

/// The code object of an instance; none for what has no MIR, and an error
/// when Cranelift rejects the function.
#[crag_db::tracked(returns(ref))]
pub fn code<'db>(
    db: &'db dyn Db,
    program: Program,
    instance: InstanceKey<'db>,
    tier: Tier,
) -> Option<Result<Code<'db>, String>> {
    let body = mir(db, program, instance, tier).as_ref()?;
    let owner = *instance.owner(db);
    let value = matches!(owner, Owner::Item(item) if *item.kind(db) == ItemKind::Value);
    let cell =
        (value && *instance.entry(db) == Entry::Body).then(|| slot_key(db, program, instance));
    let lowered = lower_to_lir(db, program, owner, body, cell);
    let settings = CodegenSettings {
        target: host().clone(),
        opt: match tier {
            Tier::Baseline => OptLevel::None,
        },
    };
    Some(
        compile(&lowered.lir, &settings)
            .map(|object| Code {
                object,
                func: func_id(instance),
                slot: slot_key(db, program, instance),
                params: lowered.lir.params,
                returns: lowered.lir.returns,
                calls: lowered.calls,
                types: lowered.types,
                unsupported: lowered.unsupported,
            })
            .map_err(|e| e.to_string()),
    )
}
