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

//! Loads hand-assembled machine code and runs it, so the loader is tested
//! without the code generator.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]

use crag_abi::{CodeObject, FuncId, Reloc, RelocKind, RelocTarget, RuntimeFn, StackCheck};
use crag_loader::{CodeAddr, CodeArena, LoadError, SymbolTable, load, load_group, unload};

const PAGE: usize = 4096;

fn object(code: Vec<u8>, relocs: Vec<Reloc>) -> CodeObject {
    CodeObject {
        code,
        align: 16,
        entry: 0,
        relocs,
        footprint: 0,
        stack_check: StackCheck::None,
        stack_maps: vec![],
    }
}

/// `mov eax, value; ret`
fn constant(value: u32) -> CodeObject {
    let mut code = vec![0xb8];
    code.extend(value.to_le_bytes());
    code.push(0xc3);
    object(code, vec![])
}

/// `movabs rax, <target>; jmp rax`
fn jump(target: RelocTarget, addend: i64) -> CodeObject {
    let mut code = vec![0x48, 0xb8];
    code.extend([0u8; 8]);
    code.extend([0xff, 0xe0]);
    object(
        code,
        vec![Reloc {
            offset: 2,
            kind: RelocKind::Abs64,
            target,
            addend,
        }],
    )
}

fn call(addr: CodeAddr) -> u32 {
    // SAFETY: every object in these tests is a complete C function without
    // parameters that returns a 32-bit value in eax.
    unsafe { std::mem::transmute::<*const u8, extern "C" fn() -> u32>(addr.as_ptr())() }
}

/// The protection of the mapping that holds `addr`, as in `/proc/self/maps`.
fn protection(addr: usize) -> String {
    let maps = std::fs::read_to_string("/proc/self/maps").unwrap();
    for line in maps.lines() {
        let mut fields = line.split_whitespace();
        let (start, end) = fields.next().unwrap().split_once('-').unwrap();
        let start = usize::from_str_radix(start, 16).unwrap();
        let end = usize::from_str_radix(end, 16).unwrap();
        if (start..end).contains(&addr) {
            return fields.next().unwrap().to_string();
        }
    }
    panic!("{addr:#x} is not mapped");
}

extern "C" fn seven() -> u32 {
    7
}

#[test]
fn loaded_code_runs_from_executable_pages() {
    let mut arena = CodeArena::new(16 * PAGE).unwrap();
    let symbols = SymbolTable::new();
    assert_eq!(protection(arena_probe(&mut arena, &symbols)), "---p");

    let addr = load(&mut arena, &symbols, &constant(42)).unwrap();
    assert_eq!(call(addr), 42);
    assert_eq!(protection(addr.addr()), "r-xp");
    assert_eq!(addr.addr() % 16, 0);
    assert_eq!(arena.bytes_in_use(), PAGE);
}

/// The address the next load will get: load, look, unload.
fn arena_probe(arena: &mut CodeArena, symbols: &SymbolTable) -> usize {
    let addr = load(arena, symbols, &constant(0)).unwrap();
    let mut scratch = SymbolTable::new();
    // SAFETY: the code was never run.
    unsafe { unload(arena, &mut scratch, addr).unwrap() };
    addr.addr()
}

#[test]
fn relocations_resolve_every_kind_of_target() {
    let mut arena = CodeArena::new(16 * PAGE).unwrap();
    let mut symbols = SymbolTable::new();
    symbols.define_runtime(RuntimeFn::Morestack, seven as *const () as usize);

    load_group(&mut arena, &mut symbols, &[(FuncId(0), &constant(42))]).unwrap();

    // 1 jumps forward to 2 in the same group; 2 jumps to 0, loaded earlier;
    // 3 jumps to itself plus an addend, which skips the jump.
    let to_member = jump(RelocTarget::Function(FuncId(2)), 0);
    let to_earlier = jump(RelocTarget::Function(FuncId(0)), 0);
    let mut to_self = jump(RelocTarget::Function(FuncId(3)), 16);
    to_self.code.resize(16, 0x90);
    to_self.code.extend(constant(43).code);
    let entries = load_group(
        &mut arena,
        &mut symbols,
        &[
            (FuncId(1), &to_member),
            (FuncId(2), &to_earlier),
            (FuncId(3), &to_self),
        ],
    )
    .unwrap();
    assert_eq!(call(entries[0]), 42);
    assert_eq!(call(entries[2]), 43);
    assert_eq!(symbols.function(FuncId(2)), Some(entries[1]));

    // A runtime function.
    let to_runtime = jump(RelocTarget::Runtime(RuntimeFn::Morestack), 0);
    assert_eq!(call(load(&mut arena, &symbols, &to_runtime).unwrap()), 7);

    // A second routine in the same object, entered at an offset: the entry
    // jumps back to the routine at the start.
    let mut two_routines = constant(44);
    two_routines.code.resize(16, 0x90);
    two_routines.entry = 16;
    two_routines
        .code
        .extend(jump(RelocTarget::Local(0), 0).code);
    two_routines.relocs.push(Reloc {
        offset: 18,
        kind: RelocKind::Abs64,
        target: RelocTarget::Local(0),
        addend: 0,
    });
    assert_eq!(call(load(&mut arena, &symbols, &two_routines).unwrap()), 44);
}

#[test]
fn failed_load_changes_nothing() {
    let mut arena = CodeArena::new(16 * PAGE).unwrap();
    let mut symbols = SymbolTable::new();
    let next = arena_probe(&mut arena, &symbols);

    let fails = |arena: &mut CodeArena, symbols: &mut SymbolTable, obj: &CodeObject| {
        let err = load_group(
            arena,
            symbols,
            &[(FuncId(5), &constant(1)), (FuncId(6), obj)],
        )
        .unwrap_err();
        assert_eq!(arena.bytes_in_use(), 0);
        assert_eq!(symbols.function(FuncId(5)), None);
        err
    };

    let err = fails(
        &mut arena,
        &mut symbols,
        &jump(RelocTarget::Function(FuncId(9)), 0),
    );
    assert!(matches!(err, LoadError::UnresolvedFunction(FuncId(9))));

    let err = fails(
        &mut arena,
        &mut symbols,
        &jump(RelocTarget::Runtime(RuntimeFn::Morestack), 0),
    );
    assert!(matches!(
        err,
        LoadError::UnresolvedRuntime(RuntimeFn::Morestack)
    ));

    let mut bad = constant(1);
    bad.entry = 6;
    assert!(matches!(
        fails(&mut arena, &mut symbols, &bad),
        LoadError::Malformed(_)
    ));
    let mut bad = constant(1);
    bad.align = 24;
    assert!(matches!(
        fails(&mut arena, &mut symbols, &bad),
        LoadError::Malformed(_)
    ));
    let mut bad = jump(RelocTarget::Function(FuncId(5)), 0);
    bad.relocs[0].offset = 5;
    assert!(matches!(
        fails(&mut arena, &mut symbols, &bad),
        LoadError::Malformed(_)
    ));
    let bad = jump(RelocTarget::Local(12), 0);
    assert!(matches!(
        fails(&mut arena, &mut symbols, &bad),
        LoadError::Malformed(_)
    ));

    // The pages of the failed attempts are free again.
    let addr = load(&mut arena, &symbols, &constant(2)).unwrap();
    assert_eq!(addr.addr(), next);
}

#[test]
fn duplicate_functions_are_rejected() {
    let mut arena = CodeArena::new(16 * PAGE).unwrap();
    let mut symbols = SymbolTable::new();
    let one = constant(1);
    load_group(&mut arena, &mut symbols, &[(FuncId(0), &one)]).unwrap();
    let again = load_group(&mut arena, &mut symbols, &[(FuncId(0), &one)]);
    assert!(matches!(
        again,
        Err(LoadError::DuplicateFunction(FuncId(0)))
    ));
    let twice = load_group(
        &mut arena,
        &mut symbols,
        &[(FuncId(1), &one), (FuncId(1), &one)],
    );
    assert!(matches!(
        twice,
        Err(LoadError::DuplicateFunction(FuncId(1)))
    ));
    assert_eq!(arena.bytes_in_use(), PAGE);
}

#[test]
fn unload_frees_a_region_with_its_last_object() {
    let mut arena = CodeArena::new(16 * PAGE).unwrap();
    let mut symbols = SymbolTable::new();
    let entries = load_group(
        &mut arena,
        &mut symbols,
        &[(FuncId(0), &constant(1)), (FuncId(1), &constant(2))],
    )
    .unwrap();

    // SAFETY: none of the code is running, and unloaded code is not called.
    unsafe {
        unload(&mut arena, &mut symbols, entries[0]).unwrap();
        assert_eq!(symbols.function(FuncId(0)), None);
        assert_eq!(symbols.function(FuncId(1)), Some(entries[1]));
        assert_eq!(arena.bytes_in_use(), PAGE);
        assert_eq!(call(entries[1]), 2);

        unload(&mut arena, &mut symbols, entries[1]).unwrap();
        assert_eq!(arena.bytes_in_use(), 0);
        assert_eq!(protection(entries[1].addr()), "---p");

        let again = unload(&mut arena, &mut symbols, entries[1]);
        assert!(matches!(again, Err(LoadError::NotLoaded(_))));
    }

    // The pages and the function number can be used again.
    let reloaded = load_group(&mut arena, &mut symbols, &[(FuncId(0), &constant(3))]).unwrap();
    assert_eq!(reloaded[0], entries[0]);
    assert_eq!(call(reloaded[0]), 3);
}

#[test]
fn freed_neighbours_merge_and_a_full_arena_reports_it() {
    let mut arena = CodeArena::new(3 * PAGE).unwrap();
    let mut symbols = SymbolTable::new();
    let a = load(&mut arena, &symbols, &constant(1)).unwrap();
    let b = load(&mut arena, &symbols, &constant(2)).unwrap();
    let c = load(&mut arena, &symbols, &constant(3)).unwrap();
    assert!(matches!(
        load(&mut arena, &symbols, &constant(4)),
        Err(LoadError::ArenaFull)
    ));

    // Two pages of code fit only where `a` and `b` were, once both are free.
    let mut large = constant(5);
    large.code.resize(PAGE + 1, 0x90);
    // SAFETY: none of the code is running, and unloaded code is not called.
    unsafe {
        unload(&mut arena, &mut symbols, b).unwrap();
        assert!(matches!(
            load(&mut arena, &symbols, &large),
            Err(LoadError::ArenaFull)
        ));
        unload(&mut arena, &mut symbols, a).unwrap();
    }
    let merged = load(&mut arena, &symbols, &large).unwrap();
    assert_eq!(merged, a);
    assert_eq!(call(merged), 5);
    assert_eq!(call(c), 3);
    assert_eq!(arena.bytes_in_use(), 3 * PAGE);
}

#[test]
fn no_page_is_writable_and_executable() {
    let mut arena = CodeArena::new(16 * PAGE).unwrap();
    let mut symbols = SymbolTable::new();
    let first = load(&mut arena, &symbols, &constant(1)).unwrap();
    let second = load_group(&mut arena, &mut symbols, &[(FuncId(0), &constant(2))]).unwrap()[0];
    // SAFETY: the code is not running and is not called again.
    unsafe { unload(&mut arena, &mut symbols, first).unwrap() };
    let third = load(&mut arena, &symbols, &constant(3)).unwrap();

    for addr in [second, third] {
        assert_eq!(protection(addr.addr()), "r-xp");
    }
    let maps = std::fs::read_to_string("/proc/self/maps").unwrap();
    let both = maps
        .lines()
        .filter(|l| l.split_whitespace().nth(1).unwrap().starts_with("rwx"));
    assert_eq!(both.count(), 0);
}
