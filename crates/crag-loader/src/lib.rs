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

//! Code loader (Implementation Plan §11.3.6).
//!
//! Copies code objects into pages, applies relocations and keeps pages
//! write-xor-execute.
//!
//! # Pages are never writable and executable at once
//!
//! Protection applies to whole pages, so the unit of loading is a *region*:
//! a run of fresh pages that one `load` or `load_group` call fills while they
//! are writable and then turns executable for good. A later load never
//! reopens them, so no thread can find code it is running made non-executable
//! under it. The price is that every call uses at least one page; code that
//! is compiled together should be loaded together.
//!
//! A region's pages return to the free list when its last code object is
//! unloaded.
//!
//! # Slots
//!
//! Development images call through a slot table (Implementation Plan
//! §11.6.4): a call loads the callee's entry from its slot and calls that,
//! so a function can be replaced by loading new code and storing its entry
//! in the slot. Every later call reaches the new code, while frames already
//! running finish on the old. A slot belongs to a function with one
//! signature, as a [`SlotKey`] names it; loading a function fills its slot.
//! The table grows in chunks that never move, so a slot's address, which
//! the code is patched with, stays valid as long as the table lives.
//!
//! # Cells
//!
//! The code that computes a module-level value keeps it in a cell
//! (Implementation Plan §11.6.2), named like a slot by that code's key.
//! Loading a group makes the cells its code names, empty; the code fills
//! its cell on the first read. The image empties a cell to have the value
//! computed again.

#![cfg(unix)]

use std::collections::{BTreeMap, HashMap, HashSet};
use std::io;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

use crag_abi::{
    CELL_EMPTY, CELL_SIZE, CodeObject, FuncId, RelocKind, RelocTarget, RuntimeFn, SlotKey,
};

/// The address of a loaded code object's entry point.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CodeAddr(usize);

impl CodeAddr {
    pub fn addr(self) -> usize {
        self.0
    }

    pub fn as_ptr(self) -> *const u8 {
        self.0 as *const u8
    }
}

/// Slots per chunk of the slot table: a page of them.
const SLOT_CHUNK: usize = 512;

/// A slot's place in the slot table, assigned when its key is first loaded
/// and kept for the table's life.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SlotIndex(u32);

/// The entry points that calls through slots load, one per function and
/// signature. An empty slot holds zero.
#[derive(Default)]
pub struct SlotTable {
    chunks: Vec<Box<[AtomicUsize; SLOT_CHUNK]>>,
    index: HashMap<SlotKey, SlotIndex>,
}

impl SlotTable {
    /// The slot of a key, if it has one.
    pub fn index(&self, key: SlotKey) -> Option<SlotIndex> {
        self.index.get(&key).copied()
    }

    /// The slot of a key, made when it has none.
    fn assign(&mut self, key: SlotKey) -> SlotIndex {
        let next = SlotIndex(self.index.len() as u32);
        let index = *self.index.entry(key).or_insert(next);
        if index == next && next.0 as usize == self.chunks.len() * SLOT_CHUNK {
            self.chunks
                .push(Box::new([const { AtomicUsize::new(0) }; SLOT_CHUNK]));
        }
        index
    }

    fn word(&self, index: SlotIndex) -> &AtomicUsize {
        let i = index.0 as usize;
        &self.chunks[i / SLOT_CHUNK][i % SLOT_CHUNK]
    }

    /// The address of a slot, which calls load the entry point from.
    pub fn address(&self, index: SlotIndex) -> usize {
        self.word(index).as_ptr() as usize
    }

    /// The entry point a key's slot holds now; none when it has no slot or
    /// the slot is empty.
    pub fn get(&self, key: SlotKey) -> Option<CodeAddr> {
        let entry = self.word(self.index(key)?).load(Ordering::Acquire);
        (entry != 0).then_some(CodeAddr(entry))
    }
}

/// Stores an entry point in a slot. The store is atomic, so a call on
/// another thread loads either the old entry or the new one.
pub fn slot_set(table: &SlotTable, index: SlotIndex, addr: CodeAddr) {
    table.word(index).store(addr.0, Ordering::Release);
}

/// Cells per chunk of the cell table: a page of them.
const CELL_CHUNK: usize = 4096 / CELL_SIZE;

/// One cell: its state word and the value's words.
type Cell = [AtomicU64; CELL_SIZE / 8];

/// The cells of module-level values, one per slot key of the code that
/// computes a value, which keeps the value there (`crag_abi::CELL_SIZE`).
/// A cell is made empty when code that names it is first loaded; like
/// slots, cells never move.
#[derive(Default)]
pub struct CellTable {
    chunks: Vec<Box<[Cell; CELL_CHUNK]>>,
    index: HashMap<SlotKey, usize>,
}

impl CellTable {
    fn assign(&mut self, key: SlotKey) -> usize {
        let next = self.index.len();
        let index = *self.index.entry(key).or_insert(next);
        if index == next && next == self.chunks.len() * CELL_CHUNK {
            self.chunks.push(Box::new(
                [const { [const { AtomicU64::new(0) }; CELL_SIZE / 8] }; CELL_CHUNK],
            ));
        }
        index
    }

    fn cell(&self, index: usize) -> &Cell {
        &self.chunks[index / CELL_CHUNK][index % CELL_CHUNK]
    }

    /// The address of a key's cell, if it has one.
    pub fn address(&self, key: SlotKey) -> Option<usize> {
        Some(self.cell(*self.index.get(&key)?).as_ptr() as usize)
    }

    /// The state of a key's cell: `CELL_EMPTY` or `CELL_FULL`.
    pub fn state(&self, key: SlotKey) -> Option<u64> {
        Some(self.cell(*self.index.get(&key)?)[0].load(Ordering::Acquire))
    }

    /// Empties a key's cell, so the value is computed again when it is next
    /// read. The value it held is not released.
    pub fn reset(&self, key: SlotKey) {
        if let Some(&index) = self.index.get(&key) {
            self.cell(index)[0].store(CELL_EMPTY, Ordering::Release);
        }
    }
}

/// What relocations resolve against: the runtime functions, the loaded
/// Crag functions, their slots and the cells of values.
#[derive(Default)]
pub struct SymbolTable {
    runtime: [Option<usize>; RuntimeFn::ALL.len()],
    functions: HashMap<FuncId, CodeAddr>,
    slots: SlotTable,
    cells: CellTable,
}

impl SymbolTable {
    pub fn new() -> SymbolTable {
        SymbolTable::default()
    }

    /// Sets the address of a runtime function. Code loaded earlier keeps the
    /// address it was patched with.
    pub fn define_runtime(&mut self, func: RuntimeFn, addr: usize) {
        self.runtime[func as usize] = Some(addr);
    }

    pub fn runtime(&self, func: RuntimeFn) -> Option<usize> {
        self.runtime[func as usize]
    }

    /// The entry point of a loaded function: its latest code.
    pub fn function(&self, func: FuncId) -> Option<CodeAddr> {
        self.functions.get(&func).copied()
    }

    pub fn slots(&self) -> &SlotTable {
        &self.slots
    }

    pub fn cells(&self) -> &CellTable {
        &self.cells
    }
}

#[derive(Debug)]
pub enum LoadError {
    /// The operating system refused to map or protect memory.
    Os(io::Error),
    /// The arena's address range is used up.
    ArenaFull,
    /// A relocation names a function that is neither loaded nor in the group.
    UnresolvedFunction(FuncId),
    /// A relocation names a runtime function with no address.
    UnresolvedRuntime(RuntimeFn),
    /// A relocation names the slot of a function with a signature that is
    /// neither loaded nor in the group.
    UnresolvedSlot(SlotKey),
    /// A relocation names the cell of a value whose code is not loaded with
    /// a group: an entry stub's.
    UnresolvedCell(SlotKey),
    /// The function is already loaded, or appears twice in the group.
    DuplicateFunction(FuncId),
    /// The code object contradicts itself: an entry point, relocation or
    /// local target outside its code, or an alignment the arena cannot give.
    Malformed(&'static str),
    /// `unload` was given an address that is not a loaded entry point.
    NotLoaded(CodeAddr),
}

impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LoadError::Os(e) => write!(f, "mapping code memory failed: {e}"),
            LoadError::ArenaFull => write!(f, "the code arena is full"),
            LoadError::UnresolvedFunction(id) => write!(f, "function {} is not loaded", id.0),
            LoadError::UnresolvedRuntime(func) => {
                write!(f, "runtime function {} has no address", func.symbol())
            }
            LoadError::UnresolvedSlot(key) => write!(
                f,
                "function {} with signature {} is not loaded",
                key.func.0, key.signature
            ),
            LoadError::UnresolvedCell(key) => write!(
                f,
                "the value of function {} with signature {} has no cell",
                key.func.0, key.signature
            ),
            LoadError::DuplicateFunction(id) => {
                write!(f, "function {} is already loaded or comes twice", id.0)
            }
            LoadError::Malformed(why) => write!(f, "malformed code object: {why}"),
            LoadError::NotLoaded(addr) => write!(f, "no code is loaded at {:#x}", addr.0),
        }
    }
}

impl std::error::Error for LoadError {}

impl From<io::Error> for LoadError {
    fn from(e: io::Error) -> LoadError {
        LoadError::Os(e)
    }
}

/// A run of pages filled by one load.
struct Region {
    len: usize,
    /// Code objects in it that are still loaded.
    live: usize,
}

/// Executable memory for code objects.
///
/// The arena reserves one contiguous address range up front, so all code
/// stays within reach of relative branches, and commits pages from it on
/// demand. Dropping the arena unmaps all of it; code loaded into it must not
/// run afterwards.
pub struct CodeArena {
    base: usize,
    reserved: usize,
    page: usize,
    /// First address never handed out.
    next: usize,
    /// Returned page runs, start to length, with neighbours merged.
    free: BTreeMap<usize, usize>,
    /// Regions in use, by start address.
    regions: HashMap<usize, Region>,
    /// Loaded entry points, each with the start of its region.
    objects: HashMap<usize, usize>,
}

// SAFETY: the arena owns its mapping and holds only addresses into it; no
// thread-specific state is involved.
unsafe impl Send for CodeArena {}

impl CodeArena {
    /// Reserves `reserve` bytes of address space, rounded up to whole pages.
    /// Reserved pages cost no memory until code is loaded into them.
    pub fn new(reserve: usize) -> io::Result<CodeArena> {
        // SAFETY: `sysconf` has no preconditions.
        let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) } as usize;
        let reserved = reserve.max(1).next_multiple_of(page);
        // SAFETY: a fresh anonymous mapping at an address the kernel picks;
        // it aliases nothing.
        let base = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                reserved,
                libc::PROT_NONE,
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_NORESERVE,
                -1,
                0,
            )
        };
        if base == libc::MAP_FAILED {
            return Err(io::Error::last_os_error());
        }
        let base = base as usize;
        Ok(CodeArena {
            base,
            reserved,
            page,
            next: base,
            free: BTreeMap::new(),
            regions: HashMap::new(),
            objects: HashMap::new(),
        })
    }

    /// Bytes in regions that hold loaded code.
    pub fn bytes_in_use(&self) -> usize {
        self.regions.values().map(|r| r.len).sum()
    }

    /// Takes `len` bytes of pages, first from the free list.
    fn alloc(&mut self, len: usize) -> Result<usize, LoadError> {
        let found = self
            .free
            .iter()
            .find(|&(_, &run)| run >= len)
            .map(|(&start, &run)| (start, run));
        if let Some((start, run)) = found {
            self.free.remove(&start);
            if run > len {
                self.free.insert(start + len, run - len);
            }
            return Ok(start);
        }
        if len > self.base + self.reserved - self.next {
            return Err(LoadError::ArenaFull);
        }
        let start = self.next;
        self.next += len;
        Ok(start)
    }

    /// Makes a page run inaccessible, gives its memory back to the operating
    /// system and puts it on the free list.
    fn release(&mut self, start: usize, len: usize) {
        // SAFETY: the run lies inside the arena's mapping and no loaded code
        // object is in it: the callers pass a region that was never
        // registered or whose last object was just unloaded.
        unsafe {
            let ptr = start as *mut libc::c_void;
            // Neither call can fail for a range inside our own mapping; if
            // one did, the pages would merely stay committed.
            libc::mprotect(ptr, len, libc::PROT_NONE);
            libc::madvise(ptr, len, libc::MADV_DONTNEED);
        }
        let (mut start, mut len) = (start, len);
        if let Some((&before, &run)) = self.free.range(..start).next_back()
            && before + run == start
        {
            self.free.remove(&before);
            start = before;
            len += run;
        }
        if let Some(run) = self.free.remove(&(start + len)) {
            len += run;
        }
        self.free.insert(start, len);
    }

    fn protect(&self, start: usize, len: usize, prot: libc::c_int) -> io::Result<()> {
        // SAFETY: the range lies inside the arena's mapping. Changing the
        // protection of a region being filled affects no running code,
        // because no entry point in it has been published yet.
        let rc = unsafe { libc::mprotect(start as *mut libc::c_void, len, prot) };
        if rc == 0 {
            Ok(())
        } else {
            Err(io::Error::last_os_error())
        }
    }
}

impl Drop for CodeArena {
    fn drop(&mut self) {
        // SAFETY: unmaps exactly the mapping `new` created.
        unsafe {
            libc::munmap(self.base as *mut libc::c_void, self.reserved);
        }
    }
}

/// Bytes that trap if executed, for the gaps between code objects.
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
const FILL: u8 = 0xCC; // int3
#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
const FILL: u8 = 0; // an undefined instruction on AArch64 and RISC-V

/// Loads one code object that no other code refers to by `FuncId`, such as an
/// entry stub. Its relocations may name functions already loaded.
pub fn load(
    arena: &mut CodeArena,
    symbols: &SymbolTable,
    code: &CodeObject,
) -> Result<CodeAddr, LoadError> {
    Ok(place(arena, symbols, &[(None, code)])?[0])
}

/// Loads functions together into one region, enters them in the symbol
/// table and fills their slots. Their relocations may name each other,
/// themselves and functions already loaded. Either all are loaded or none.
pub fn load_group(
    arena: &mut CodeArena,
    symbols: &mut SymbolTable,
    group: &[(SlotKey, &CodeObject)],
) -> Result<Vec<CodeAddr>, LoadError> {
    enter(arena, symbols, group, false)
}

/// Loads functions as `load_group` does, except that some may be loaded
/// already: their new code takes their place in the symbol table and their
/// slots, so later calls through the slots reach it. The old code stays
/// loaded, since frames may still run it; it is not unloaded yet.
pub fn replace_group(
    arena: &mut CodeArena,
    symbols: &mut SymbolTable,
    group: &[(SlotKey, &CodeObject)],
) -> Result<Vec<CodeAddr>, LoadError> {
    enter(arena, symbols, group, true)
}

fn enter(
    arena: &mut CodeArena,
    symbols: &mut SymbolTable,
    group: &[(SlotKey, &CodeObject)],
    replace: bool,
) -> Result<Vec<CodeAddr>, LoadError> {
    let mut seen = HashSet::new();
    for &(key, _) in group {
        let loaded = !replace && symbols.functions.contains_key(&key.func);
        if loaded || !seen.insert(key.func) {
            return Err(LoadError::DuplicateFunction(key.func));
        }
    }
    // The members' slots must exist before their callers are patched with
    // the slots' addresses. If the load fails, they stay empty.
    let slots: Vec<SlotIndex> = group
        .iter()
        .map(|&(key, _)| symbols.slots.assign(key))
        .collect();
    for (_, code) in group {
        for reloc in &code.relocs {
            if let RelocTarget::Cell(key) = reloc.target {
                symbols.cells.assign(key);
            }
        }
    }
    let items: Vec<_> = group.iter().map(|&(key, code)| (Some(key), code)).collect();
    let entries = place(arena, symbols, &items)?;
    // The code is executable now, so it may be published.
    for ((&(key, _), &entry), &slot) in group.iter().zip(&entries).zip(&slots) {
        symbols.functions.insert(key.func, entry);
        slot_set(&symbols.slots, slot, entry);
    }
    Ok(entries)
}

/// Allocates a region, copies the objects in, relocates and protects.
fn place(
    arena: &mut CodeArena,
    symbols: &SymbolTable,
    items: &[(Option<SlotKey>, &CodeObject)],
) -> Result<Vec<CodeAddr>, LoadError> {
    // Lay the objects out one after another.
    let mut offsets = Vec::with_capacity(items.len());
    let mut size = 0usize;
    for (_, obj) in items {
        let align = obj.align.max(1) as usize;
        if !align.is_power_of_two() || align > arena.page {
            return Err(LoadError::Malformed(
                "alignment is not a power of two within a page",
            ));
        }
        if obj.entry as usize >= obj.code.len() {
            return Err(LoadError::Malformed("entry point outside the code"));
        }
        size = size.next_multiple_of(align);
        offsets.push(size);
        size += obj.code.len();
    }
    if items.is_empty() {
        return Ok(Vec::new());
    }
    let len = size.next_multiple_of(arena.page);

    // Resolve every relocation before touching memory, so a failure leaves
    // the arena as it was.
    let start = arena.alloc(len)?;
    let entry_of = |i: usize| start + offsets[i] + items[i].1.entry as usize;
    let mut patches = Vec::new();
    let resolved = (|| {
        for (i, (_, obj)) in items.iter().enumerate() {
            for reloc in &obj.relocs {
                let RelocKind::Abs64 = reloc.kind;
                if reloc.offset as usize + 8 > obj.code.len() {
                    return Err(LoadError::Malformed("relocation outside the code"));
                }
                let target = match reloc.target {
                    RelocTarget::Function(id) => {
                        let member = items
                            .iter()
                            .position(|&(member, _)| member.is_some_and(|key| key.func == id));
                        match member {
                            Some(member) => entry_of(member),
                            None => symbols
                                .function(id)
                                .ok_or(LoadError::UnresolvedFunction(id))?
                                .addr(),
                        }
                    }
                    RelocTarget::Slot(key) => {
                        let member = items.iter().any(|&(member, _)| member == Some(key));
                        let slots = &symbols.slots;
                        match slots.index(key) {
                            Some(slot) if member || slots.get(key).is_some() => slots.address(slot),
                            _ => return Err(LoadError::UnresolvedSlot(key)),
                        }
                    }
                    RelocTarget::Cell(key) => symbols
                        .cells
                        .address(key)
                        .ok_or(LoadError::UnresolvedCell(key))?,
                    RelocTarget::Runtime(func) => symbols
                        .runtime(func)
                        .ok_or(LoadError::UnresolvedRuntime(func))?,
                    RelocTarget::Local(offset) => {
                        if offset as usize >= obj.code.len() {
                            return Err(LoadError::Malformed("local target outside the code"));
                        }
                        start + offsets[i] + offset as usize
                    }
                };
                let value = (target as u64).wrapping_add_signed(reloc.addend);
                patches.push((start + offsets[i] + reloc.offset as usize, value));
            }
        }
        Ok(())
    })();
    if let Err(e) =
        resolved.and_then(|()| Ok(arena.protect(start, len, libc::PROT_READ | libc::PROT_WRITE)?))
    {
        arena.release(start, len);
        return Err(e);
    }

    // SAFETY: the region `start..start + len` is ours alone and writable.
    // Every copy and patch stays inside it: the offsets were laid out within
    // `size <= len`, and each patch was checked against its object's length.
    unsafe {
        std::ptr::write_bytes(start as *mut u8, FILL, len);
        for ((_, obj), &offset) in items.iter().zip(&offsets) {
            std::ptr::copy_nonoverlapping(
                obj.code.as_ptr(),
                (start + offset) as *mut u8,
                obj.code.len(),
            );
        }
        for &(addr, value) in &patches {
            (addr as *mut u64).write_unaligned(value.to_le());
        }
    }

    if let Err(e) = arena.protect(start, len, libc::PROT_READ | libc::PROT_EXEC) {
        arena.release(start, len);
        return Err(e.into());
    }
    flush_instruction_cache(start, len);

    arena.regions.insert(
        start,
        Region {
            len,
            live: items.len(),
        },
    );
    let entries: Vec<_> = (0..items.len()).map(|i| CodeAddr(entry_of(i))).collect();
    for entry in &entries {
        arena.objects.insert(entry.0, start);
    }
    Ok(entries)
}

/// x86 keeps its instruction cache coherent by itself. Other architectures
/// need an explicit flush before new code runs.
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn flush_instruction_cache(_start: usize, _len: usize) {}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
compile_error!("the loader needs an instruction-cache flush for this architecture");

/// Unloads the code object with this entry point and removes it from the
/// symbol table. The pages go back to the free list once every object loaded
/// with it is unloaded too.
///
/// # Safety
///
/// No frame of the code may be on any stack, and nothing may call or jump to
/// it afterwards. That includes other loaded code whose relocations were
/// resolved to it.
pub unsafe fn unload(
    arena: &mut CodeArena,
    symbols: &mut SymbolTable,
    entry: CodeAddr,
) -> Result<(), LoadError> {
    let start = arena
        .objects
        .remove(&entry.0)
        .ok_or(LoadError::NotLoaded(entry))?;
    symbols.functions.retain(|_, addr| *addr != entry);
    for &slot in symbols.slots.index.values() {
        let word = symbols.slots.word(slot);
        // Nothing may call the code any more, so its slots empty.
        let _ = word.compare_exchange(entry.0, 0, Ordering::AcqRel, Ordering::Relaxed);
    }
    let region = arena
        .regions
        .get_mut(&start)
        .expect("a loaded object has a region");
    region.live -= 1;
    if region.live == 0 {
        let len = region.len;
        arena.regions.remove(&start);
        arena.release(start, len);
    }
    Ok(())
}
