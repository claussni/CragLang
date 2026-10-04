//! Code generation facade (Implementation Plan §11.3.5).
//!
//! Lowers `LirFunction` to a `CodeObject` through Cranelift. No Cranelift type
//! may appear in this crate's public interface.
