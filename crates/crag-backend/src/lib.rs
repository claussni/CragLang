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
//! `layout` decides how. Boxes are allocated, retained and released, and
//! checks trap, through calls of the runtime. Every call is a safepoint
//! whose stack map lists the boxes the frame holds.

extern crate crag_db as salsa;

mod layout;
mod lower;

use std::sync::OnceLock;

use crag_codegen::{CodeObject, CodegenSettings, OptLevel, Target, compile, target_for};
use crag_db::Db;
use crag_hir::Program;
use crag_mir::{InstanceKey, Tier, mir};

pub use layout::{FieldSlot, Layout, layout, record_layout, type_index};
pub use lower::{Lowered, func_id, lower_to_lir};

/// The code of an instance, ready for the loader.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Code<'db> {
    pub object: CodeObject,
    /// The function the object is loaded as, which calls name.
    pub func: crag_codegen::FuncId,
    /// Words of parameters and results, for the entry stub.
    pub params: u32,
    pub returns: u32,
    /// The instances it calls, which must be loaded with it.
    pub calls: Vec<InstanceKey<'db>>,
    /// What it could not compile; each traps where it is reached.
    pub unsupported: Vec<&'static str>,
}

/// The target code is generated for: the host's.
fn host() -> &'static Target {
    static HOST: OnceLock<Target> = OnceLock::new();
    HOST.get_or_init(|| target_for("x86_64-unknown-linux-gnu").expect("the host is supported"))
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
    let lowered = lower_to_lir(db, program, body);
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
                params: lowered.lir.params,
                returns: lowered.lir.returns,
                calls: lowered.calls,
                unsupported: lowered.unsupported,
            })
            .map_err(|e| e.to_string()),
    )
}
