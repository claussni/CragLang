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
//! signature: a hash of the function type its MIR has, parameters and
//! result, with every declared type spelled out to its fields. It stays
//! the same while the signature and the layouts of what passes through it
//! do. So a reload never lets running code call new code that lays out
//! its arguments or result otherwise: a function whose types changed gets
//! another slot, which only new code calls (§11.8.5).
//!
//! A read of a module-level value calls the code that computes it. That
//! code keeps the value in a cell the loader makes, and gives what the cell
//! holds once it is full (Implementation Plan §11.6.2).

extern crate crag_db as salsa;

pub mod flat;
mod layout;
mod lower;
mod shape;
mod split;

use std::collections::HashMap;
use std::sync::OnceLock;

use crag_abi::{SlotKey, TypeDescriptor};

use crag_codegen::{CodeObject, CodegenSettings, OptLevel, Target, compile, target_for};
use crag_db::Db;
use crag_hir::{Owner, Program};
use crag_mir::{Entry, InstanceKey, Tier, mir};
use crag_types::{Ty, TyKind};

pub use layout::{
    FieldSlot, Layout, element_layout, layout, record_layout, type_descriptor, type_index,
};
pub use lower::{Lowered, StepInfo, func_id, lower_to_lir};
pub use shape::{shapes, split_shapes};
pub use split::{flat_layouts, flat_params, flat_result, scalar_replace};

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
    /// Its steps, for the debugger.
    pub steps: Vec<StepInfo<'db>>,
}

/// A store of compiled code that outlives the process (Implementation
/// Plan §11.9.5). Cranelift's output follows from the LIR and the settings
/// alone, so their text is the whole input; the cache adds the compiler's
/// identity to its key.
pub trait CodeCache: Send + Sync {
    fn get(&self, input: &str) -> Option<CodeObject>;
    fn put(&self, input: &str, object: &CodeObject);
}

static CODE_CACHE: OnceLock<Box<dyn CodeCache>> = OnceLock::new();

/// Makes `code` look for compiled code in `cache` before compiling, and
/// keep what it compiles there. Once per process; false when a cache is
/// installed already.
pub fn install_code_cache(cache: Box<dyn CodeCache>) -> bool {
    CODE_CACHE.set(cache).is_ok()
}

/// Compiles, or takes the object a cache kept for the same input.
///
/// Function ids are numbered as the database met the instances, so the
/// same function has other ids in other programs. The cache's input
/// therefore numbers them by their first appearance in the LIR, and the
/// object it keeps names them by those numbers, tagged, in its
/// relocations; code holds them nowhere else.
fn compile_cached(
    lir: &crag_codegen::LirFunction,
    settings: &CodegenSettings,
) -> Result<CodeObject, String> {
    let Some(cache) = CODE_CACHE.get() else {
        return compile(lir, settings).map_err(|e| e.to_string());
    };
    let text = format!(
        "{HOST_TRIPLE} {:?} {}\n{lir:?}",
        settings.opt, settings.metered
    );
    let Some((input, ids)) = canonical(&text) else {
        return compile(lir, settings).map_err(|e| e.to_string());
    };
    if let Some(mut object) = cache.get(&input) {
        let restored = renumber(&mut object, |id| match id & CANONICAL {
            0 => None,
            _ => ids.get((id & !CANONICAL) as usize).copied(),
        });
        if restored.is_some() {
            return Ok(object);
        }
    }
    let object = compile(lir, settings).map_err(|e| e.to_string())?;
    let mut kept = object.clone();
    let numbers: HashMap<u32, u32> = ids
        .iter()
        .enumerate()
        .map(|(i, &id)| (id, i as u32))
        .collect();
    if renumber(&mut kept, |id| numbers.get(&id).map(|i| i | CANONICAL)).is_some() {
        cache.put(&input, &kept);
    }
    Ok(object)
}

/// The tag of a function number in a kept object.
const CANONICAL: u32 = 1 << 31;

/// The text with every `FuncId(n)` numbered by its first appearance, and
/// the ids in that order; none when an id has the tag's bit, which ids
/// never have in practice.
fn canonical(text: &str) -> Option<(String, Vec<u32>)> {
    const OPEN: &str = "FuncId(";
    let mut out = String::with_capacity(text.len());
    let mut ids: Vec<u32> = Vec::new();
    let mut rest = text;
    while let Some(at) = rest.find(OPEN) {
        out.push_str(&rest[..at + OPEN.len()]);
        rest = &rest[at + OPEN.len()..];
        let end = rest.find(')')?;
        let id: u32 = rest[..end].parse().ok()?;
        if id & CANONICAL != 0 {
            return None;
        }
        let number = match ids.iter().position(|&i| i == id) {
            Some(n) => n,
            None => {
                ids.push(id);
                ids.len() - 1
            }
        };
        out.push('#');
        out.push_str(&number.to_string());
        rest = &rest[end..];
    }
    out.push_str(rest);
    Some((out, ids))
}

/// Maps the function ids of an object's relocations; none when one has no
/// image under `map`.
fn renumber(object: &mut CodeObject, map: impl Fn(u32) -> Option<u32>) -> Option<()> {
    use crag_abi::{FuncId, RelocTarget};
    for reloc in &mut object.relocs {
        match &mut reloc.target {
            RelocTarget::Function(FuncId(id)) => *id = map(*id)?,
            RelocTarget::Slot(key) | RelocTarget::Cell(key) => key.func.0 = map(key.func.0)?,
            RelocTarget::Runtime(_)
            | RelocTarget::Local(_)
            | RelocTarget::Native(_)
            | RelocTarget::NativeLibrary(_) => {}
        }
    }
    Some(())
}

const HOST_TRIPLE: &str = "x86_64-unknown-linux-gnu";

/// The target code is generated for: the host's.
fn host() -> &'static Target {
    static HOST: OnceLock<Target> = OnceLock::new();
    HOST.get_or_init(|| target_for(HOST_TRIPLE).expect("the host is supported"))
}

/// The slot of an instance: its function id and its signature.
pub fn slot_key<'db>(db: &'db dyn Db, program: Program, instance: InstanceKey<'db>) -> SlotKey {
    SlotKey {
        func: func_id(instance),
        signature: *slot_signature(db, program, instance),
    }
}

/// The signature part of an instance's slot: a hash of the function type
/// of its MIR with the fields of its types, or zero for what has none. A
/// query of its own, so that callers depend on the signature and not on
/// the body.
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
    let mut hash = structure(db, program, ty, &mut Vec::new(), &mut HashMap::new());
    // A parameter that passes by value in storage form (Plan §11.10.10),
    // as it is stored.
    for (param, &flat) in body.locals.iter().zip(flat_params(db, program, instance)) {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::hash::DefaultHasher::new();
        hash.hash(&mut hasher);
        flat.then(|| split::storage(db, program, param.ty))
            .hash(&mut hasher);
        hash = hasher.finish();
    }
    {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::hash::DefaultHasher::new();
        hash.hash(&mut hasher);
        split::flat_result(db, program, instance).hash(&mut hasher);
        hash = hasher.finish();
    }
    // Zero is for what has no signature, and the top bit for steps.
    (((hash >> 32) as u32 ^ hash as u32) & !crag_abi::STEP_CELL).max(1)
}

/// A hash of a type as it is laid out: a declared type by its name and its
/// fields, in order, with theirs. A type met again within itself is hashed
/// by its name alone. `memo` holds the hashes made so far, so a type the
/// others share is spelled out once.
fn structure<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
    open: &mut Vec<Ty<'db>>,
    memo: &mut HashMap<Ty<'db>, u64>,
) -> u64 {
    use std::hash::{Hash, Hasher};
    if let Some(&hash) = memo.get(&ty) {
        return hash;
    }
    let mut hasher = std::hash::DefaultHasher::new();
    let mut list =
        |types: &[Ty<'db>], open: &mut Vec<Ty<'db>>, hasher: &mut std::hash::DefaultHasher| {
            types.len().hash(hasher);
            for &t in types {
                structure(db, program, t, open, memo).hash(hasher);
            }
        };
    let mut cut = false;
    match ty.kind(db) {
        TyKind::Error => 0u8.hash(&mut hasher),
        TyKind::Builtin(builtin, args) => {
            1u8.hash(&mut hasher);
            format!("{builtin:?}").hash(&mut hasher);
            list(args, open, &mut hasher);
        }
        TyKind::Named(item, args) => {
            2u8.hash(&mut hasher);
            item.module(db).path(db).hash(&mut hasher);
            item.name(db).text(db).hash(&mut hasher);
            item.ordinal(db).hash(&mut hasher);
            list(args, open, &mut hasher);
            if open.contains(&ty) {
                cut = true;
            } else {
                open.push(ty);
                match record_layout(db, program, ty) {
                    Some((slots, size)) => {
                        size.hash(&mut hasher);
                        for slot in slots {
                            slot.name.text(db).hash(&mut hasher);
                            slot.offset.hash(&mut hasher);
                            structure(db, program, slot.ty, open, memo).hash(&mut hasher);
                        }
                    }
                    None => 0u32.hash(&mut hasher),
                }
                open.pop();
            }
        }
        TyKind::Record { fields, open: rest } => {
            3u8.hash(&mut hasher);
            rest.hash(&mut hasher);
            fields.len().hash(&mut hasher);
            for (name, t) in fields {
                name.text(db).hash(&mut hasher);
                structure(db, program, *t, open, memo).hash(&mut hasher);
            }
        }
        TyKind::Fn {
            params,
            result,
            pure,
        } => {
            4u8.hash(&mut hasher);
            pure.hash(&mut hasher);
            list(params, open, &mut hasher);
            structure(db, program, *result, open, memo).hash(&mut hasher);
        }
        TyKind::Union(members) => {
            5u8.hash(&mut hasher);
            list(members, open, &mut hasher);
        }
        TyKind::Param(_, index, name) => {
            6u8.hash(&mut hasher);
            index.hash(&mut hasher);
            name.text(db).hash(&mut hasher);
        }
    }
    let hash = hasher.finish();
    // A type cut short within itself is not the whole type.
    if !cut {
        memo.insert(ty, hash);
    }
    hash
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
    let mut body = mir(db, program, instance, tier).as_ref()?.clone();
    scalar_replace(db, program, instance, &mut body);
    let owner = *instance.owner(db);
    let value = matches!(owner, Owner::Item(item) if item.kind(db).is_value());
    let cell =
        (value && *instance.entry(db) == Entry::Body).then(|| slot_key(db, program, instance));
    let lowered = lower_to_lir(db, program, instance, &body, cell);
    let settings = CodegenSettings {
        target: host().clone(),
        opt: OptLevel::None,
        metered: tier == Tier::Metered,
    };
    Some(compile_cached(&lowered.lir, &settings).map(|mut object| {
        object.module = lowered.module.clone();
        object.origins = lowered.origins.clone();
        object.details = lowered.details.clone();
        Code {
            object,
            func: func_id(instance),
            slot: slot_key(db, program, instance),
            params: lowered.lir.params,
            returns: lowered.lir.returns,
            calls: lowered.calls,
            types: lowered.types,
            unsupported: lowered.unsupported,
            steps: lowered.steps,
        }
    }))
}
