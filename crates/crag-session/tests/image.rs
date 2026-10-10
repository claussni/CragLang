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

//! What an image refuses, answered in this process.

use crag_abi::{
    CodeObject, CountedField, FuncId, Reloc, RelocKind, RelocTarget, StackCheck, TypeDescriptor,
};
use crag_session::{Image, Message, ShippedFunction};

/// A function that returns at once, with the relocations given.
fn function(id: u32, params: u32, relocs: Vec<Reloc>) -> ShippedFunction {
    ShippedFunction {
        id: FuncId(id),
        signature: params,
        params,
        returns: 1,
        object: CodeObject {
            code: vec![0xc3; 16],
            align: 16,
            entry: 0,
            relocs,
            footprint: 16,
            stack_check: StackCheck::Margin,
            stack_maps: Vec::new(),
        },
    }
}

fn load(types: Vec<(u32, TypeDescriptor)>, functions: Vec<ShippedFunction>) -> Message {
    Message::Load {
        types,
        stubs: Vec::new(),
        functions,
        reset: Vec::new(),
    }
}

fn record(counted: Vec<CountedField>) -> TypeDescriptor {
    TypeDescriptor::Record { counted }
}

#[test]
fn an_image_refuses_what_it_cannot_do() {
    let mut image = Image::new().unwrap();
    assert_eq!(image.answer(Message::Ping(1)), Some(Message::Pong(1)));
    assert_eq!(image.answer(Message::Shutdown), None);
    assert_eq!(
        image.answer(Message::Run(FuncId(5))),
        Some(Message::Failed("function 5 is not loaded".into()))
    );
    assert_eq!(
        image.answer(load(
            vec![(3, record(Vec::new()))],
            vec![function(5, 1, Vec::new())]
        )),
        Some(Message::Loaded)
    );
    assert_eq!(
        image.answer(Message::Run(FuncId(5))),
        Some(Message::Failed("function 5 takes parameters".into()))
    );
    // A function the group does not hold and the image has not loaded.
    let calls = |target| Reloc {
        offset: 8,
        kind: RelocKind::Abs64,
        target: RelocTarget::Function(FuncId(target)),
        addend: 0,
    };
    assert_eq!(
        image.answer(load(Vec::new(), vec![function(6, 0, vec![calls(7)])])),
        Some(Message::Failed(
            "cannot load the code: function 7 is not loaded".into()
        ))
    );
    assert_eq!(
        image.answer(Message::Run(FuncId(6))),
        Some(Message::Failed("function 6 is not loaded".into()))
    );
    assert_eq!(
        image.answer(load(Vec::new(), vec![function(6, 0, vec![calls(5)])])),
        Some(Message::Loaded)
    );
    assert_eq!(
        image.answer(Message::Run(FuncId(6))),
        Some(Message::Failed("no entry stub returns 1 words".into()))
    );
    // Twice in one shipment, and a type index with another descriptor.
    let twice = vec![function(5, 0, Vec::new()), function(5, 0, Vec::new())];
    assert_eq!(
        image.answer(load(Vec::new(), twice)),
        Some(Message::Failed(
            "cannot load the code: function 5 is already loaded or comes twice".into()
        ))
    );
    assert_eq!(
        image.answer(Message::Run(FuncId(5))),
        Some(Message::Failed("function 5 takes parameters".into()))
    );
    assert_eq!(
        image.answer(load(
            vec![(3, record(vec![CountedField::Box(16)]))],
            vec![function(8, 0, Vec::new())]
        )),
        Some(Message::Failed(
            "type 3 has another descriptor already".into()
        ))
    );
    assert_eq!(
        image.answer(Message::Run(FuncId(8))),
        Some(Message::Failed("function 8 is not loaded".into()))
    );
    assert_eq!(
        image.answer(Message::Loaded),
        Some(Message::Failed("an image does not take Loaded".into()))
    );
    // Shipped again, a function replaces its code.
    assert_eq!(
        image.answer(load(Vec::new(), vec![function(5, 0, Vec::new())])),
        Some(Message::Loaded)
    );
    assert_eq!(
        image.answer(Message::Run(FuncId(5))),
        Some(Message::Failed("no entry stub returns 1 words".into()))
    );
}
