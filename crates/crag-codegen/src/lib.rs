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

pub use crag_abi::{CodeObject, FuncId, Reloc, RelocKind, RelocTarget, StackCheck, StackMap};
pub use lir::{BinOp, Block, BlockId, Cond, Inst, LirFunction, Term, VReg};
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
