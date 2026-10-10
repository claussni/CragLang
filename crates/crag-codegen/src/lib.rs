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

//! Code generation facade (Implementation Plan §11.3.5).
//!
//! Lowers `LirFunction` to a `CodeObject` through Cranelift. No Cranelift type
//! may appear in this crate's public interface.
//!
//! Every function this crate compiles starts with the stack check described
//! in `crag_abi`. The facade emits it; producers of LIR only mark loop
//! back-edges with [`Inst::Poll`].
//!
//! Not built yet: frame tables and typed virtual registers. Every value is
//! one machine word; `LirFunction::tracked` names the registers that hold
//! owned values and appear in stack maps.

mod lir;
mod lower;

pub use crag_abi::{
    CodeObject, FuncId, Reloc, RelocKind, RelocTarget, RuntimeFn, SlotKey, StackCheck, StackMap,
    TrapKind,
};
pub use lir::{BinOp, Block, BlockId, CallTarget, Cond, Inst, LirFunction, OverflowOp, Term, VReg};
pub use lower::{Target, UnknownTarget, compile, compile_entry_stub, target_for};

/// How much the backend optimizes (Compiler Architecture §5).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OptLevel {
    /// The baseline tier: Cranelift's fast setting.
    None,
    /// The optimizing and release tiers: Cranelift's speed setting.
    Speed,
}

/// Everything `compile` needs besides the function.
#[derive(Clone)]
pub struct CodegenSettings {
    pub target: Target,
    pub opt: OptLevel,
}

#[derive(Debug)]
pub enum CodegenError {
    /// The LIR is malformed.
    InvalidLir(String),
    /// Cranelift rejected the function.
    Backend(String),
    /// The backend asked for a relocation the loader does not support.
    UnsupportedRelocation(String),
    /// Even the wrapper for the sized check does not fit the frame budget,
    /// which happens only with very many stack-passed arguments.
    FrameTooLarge { footprint: u32, budget: u32 },
}

impl std::fmt::Display for CodegenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CodegenError::InvalidLir(why) => write!(f, "invalid LIR: {why}"),
            CodegenError::Backend(why) => write!(f, "backend error: {why}"),
            CodegenError::UnsupportedRelocation(what) => {
                write!(f, "unsupported relocation: {what}")
            }
            CodegenError::FrameTooLarge { footprint, budget } => write!(
                f,
                "frame footprint of {footprint} bytes exceeds the budget of {budget} bytes"
            ),
        }
    }
}

impl std::error::Error for CodegenError {}
