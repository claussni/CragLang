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

//! The item tree (Implementation Plan §11.4.4): what a module declares and
//! the signatures it declares them with, but not the bodies.
//!
//! The item tree is the main incremental firewall. It holds no positions,
//! and signatures are kept as syntax without trivia, so an edit inside a
//! body, or to the layout or comments of a signature, leaves the tree equal
//! and stops recomputation of everything that reads it. A declaration is
//! found again in the syntax tree by its index among the module's
//! declarations.

use std::collections::HashMap;

use crag_db::Db;
use crag_syntax::{GreenElement, GreenNode, LeafKind, SyntaxKind as S, SyntaxNode, TokenKind as T};

use crate::input::{ModuleId, parse};
use crate::patterns;

/// An identifier, stored once.
#[crag_db::interned(debug)]
pub struct Name<'db> {
    #[returns(ref)]
    pub text: String,
}

/// What an item declares.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ItemKind {
    Type,
    Form,
    Function,
    /// A module-level `let` binding (§5.5).
    Value,
    /// An `embed` declaration: a module-level value whose content comes
    /// from a resource (§18.4.1).
    Embed,
    /// A function a form requires (§4.1). It is no name of the module's
    /// scope: a generic function sees it through its bounds.
    Slot,
}

impl ItemKind {
    /// Whether the item is a module-level value: a `let`'s or an
    /// `embed`'s.
    pub fn is_value(self) -> bool {
        matches!(self, ItemKind::Value | ItemKind::Embed)
    }
}

/// An item, stable across edits to bodies: its module, name and kind, and
/// for overloads (§5.6.1) its place among the items of the same name and
/// kind.
#[crag_db::interned(debug)]
pub struct ItemId<'db> {
    pub module: ModuleId,
    pub name: Name<'db>,
    pub kind: ItemKind,
    pub ordinal: u32,
}

/// The declarations of one module.
#[derive(Clone, Debug, Default, PartialEq, Eq, crag_db::SalsaValue)]
pub struct ItemTree<'db> {
    pub imports: Vec<Import<'db>>,
    /// Types, forms, functions, values and `embed` declarations, in source
    /// order.
    pub items: Vec<Item<'db>>,
    pub tests: Vec<Test<'db>>,
    /// The functions forms require, in source order.
    pub slots: Vec<SlotItem<'db>>,
}

/// A function a form requires: the form, and its place among the form's
/// functions.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct SlotItem<'db> {
    pub id: ItemId<'db>,
    pub form: ItemId<'db>,
    pub index: u32,
}

/// The form a slot belongs to, and its place among the form's functions.
pub fn slot_item<'db>(db: &'db dyn Db, slot: ItemId<'db>) -> Option<(ItemId<'db>, u32)> {
    item_tree(db, *slot.module(db))
        .slots
        .iter()
        .find(|s| s.id == slot)
        .map(|s| (s.form, s.index))
}

/// The functions a form requires, in order.
pub fn form_slots<'db>(db: &'db dyn Db, form: ItemId<'db>) -> Vec<ItemId<'db>> {
    item_tree(db, *form.module(db))
        .slots
        .iter()
        .filter(|s| s.form == form)
        .map(|s| s.id)
        .collect()
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Item<'db> {
    pub id: ItemId<'db>,
    pub public: bool,
    /// The index of the declaration among the module's declarations.
    pub decl: u32,
    /// The declaration without its body and trivia: a function without its
    /// block, a `let` without its value, anything else whole.
    pub signature: GreenNode,
}

impl Item<'_> {
    /// Whether the declaration is `final`: no overload may outrank it
    /// (Specification §5.6.1).
    pub fn is_final(&self) -> bool {
        self.signature
            .children()
            .iter()
            .any(|e| matches!(e, GreenElement::Token(t) if t.kind() == LeafKind::Token(T::Final)))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum Import<'db> {
    /// `import a.b`, `import a.b as c` or `import a.b.{c, d as e}` (§14.2).
    Module {
        path: Vec<Name<'db>>,
        alias: Option<Name<'db>>,
        items: Option<Vec<ImportItem<'db>>>,
        decl: u32,
    },
    /// `import cLib("…").{ … }` (§16.4). Its functions are items of the
    /// module.
    C {
        /// The library's name, the string literal's text.
        library: String,
        functions: Vec<Item<'db>>,
        /// Which of the functions capture `errno` (§16.3).
        errno: Vec<bool>,
        /// The library's thread-safety marker (§16.4).
        threading: Threading,
        decl: u32,
    },
}

/// How calls of a C library may run (§16.4).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum Threading {
    #[default]
    Unsafe,
    Safe,
    Bound,
}

impl Threading {
    pub fn name(self) -> &'static str {
        match self {
            Threading::Unsafe => "ThreadUnsafe",
            Threading::Safe => "ThreadSafe",
            Threading::Bound => "ThreadBound",
        }
    }
}

/// What a C function's import says about it beyond its signature.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct CFunction {
    pub library: String,
    pub threading: Threading,
    pub errno: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct ImportItem<'db> {
    pub name: Name<'db>,
    pub alias: Option<Name<'db>>,
}

/// A `test` declaration (§5.7).
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Test<'db> {
    pub id: TestId<'db>,
    pub decl: u32,
}

/// A test, stable across edits to bodies: its module, its string literal
/// as written, and its place among the module's tests with that literal.
#[crag_db::interned(debug)]
pub struct TestId<'db> {
    pub module: ModuleId,
    #[returns(ref)]
    pub label: String,
    pub ordinal: u32,
}

/// The function a `cLib` import binds, with the declaration of the import
/// and its index among the import's functions (§16.1).
pub fn c_function<'db>(db: &'db dyn Db, item: ItemId<'db>) -> Option<(u32, usize)> {
    item_tree(db, *item.module(db))
        .imports
        .iter()
        .find_map(|import| match import {
            Import::C {
                functions, decl, ..
            } => functions
                .iter()
                .position(|f| f.id == item)
                .map(|index| (*decl, index)),
            Import::Module { .. } => None,
        })
}

/// The library, thread safety and `errno` capture of a C function.
pub fn c_function_info<'db>(db: &'db dyn Db, item: ItemId<'db>) -> Option<CFunction> {
    item_tree(db, *item.module(db))
        .imports
        .iter()
        .find_map(|import| match import {
            Import::C {
                library,
                functions,
                errno,
                threading,
                ..
            } => functions
                .iter()
                .position(|f| f.id == item)
                .map(|index| CFunction {
                    library: library.clone(),
                    threading: *threading,
                    errno: errno[index],
                }),
            Import::Module { .. } => None,
        })
}

/// The names of the markers of an `is` clause among a node's children.
fn marker_names(node: &SyntaxNode) -> Vec<String> {
    node.children()
        .filter(|n| n.kind() == S::IsClause)
        .flat_map(|clause| {
            clause
                .descendants()
                .filter(|n| n.kind() == S::Marker)
                .collect::<Vec<_>>()
        })
        .map(|m| m.text().trim().to_string())
        .collect()
}

/// The number of type parameters a function or type signature declares.
pub fn type_param_count(signature: &GreenNode) -> usize {
    SyntaxNode::new_root(signature.clone())
        .children()
        .find(|n| n.kind() == S::TypeParams)
        .map_or(0, |params| params.children().count())
}

/// Reads a module's declarations from its syntax tree. Declarations whose
/// name is missing are left out; the parser reported them.
#[crag_db::tracked(returns(ref))]
pub fn item_tree<'db>(db: &'db dyn Db, module: ModuleId) -> ItemTree<'db> {
    let root = SyntaxNode::new_root(parse(db, *module.file(db)).green.clone());
    let mut collector = Collector {
        db,
        module,
        ordinals: HashMap::new(),
        tree: ItemTree::default(),
    };
    for (decl, node) in root.children().enumerate() {
        collector.declaration(decl as u32, &node);
    }
    collector.tree
}

struct Collector<'db> {
    db: &'db dyn Db,
    module: ModuleId,
    ordinals: HashMap<(Name<'db>, ItemKind), u32>,
    tree: ItemTree<'db>,
}

impl<'db> Collector<'db> {
    fn declaration(&mut self, decl: u32, node: &SyntaxNode) {
        let whole = || node.green().without_trivia();
        match node.kind() {
            S::Import => {
                let import = self.import(decl, node);
                self.tree.imports.push(import);
            }
            S::CImport => {
                let library = node
                    .children()
                    .find(|n| matches!(n.kind(), S::Literal | S::StrExpr))
                    .map_or_else(String::new, |n| n.text());
                let library = library.trim().trim_matches('"').to_string();
                let mut errno = Vec::new();
                let functions = node
                    .children()
                    .filter(|n| n.kind() == S::CSig)
                    .filter_map(|sig| {
                        let signature = sig.green().without_trivia();
                        let item = self.item(ItemKind::Function, &sig, false, decl, signature)?;
                        errno.push(marker_names(&sig).iter().any(|m| m == "Errno"));
                        Some(item)
                    })
                    .collect();
                let threading = marker_names(node)
                    .iter()
                    .find_map(|m| match m.as_str() {
                        "ThreadSafe" => Some(Threading::Safe),
                        "ThreadBound" => Some(Threading::Bound),
                        "ThreadUnsafe" => Some(Threading::Unsafe),
                        _ => None,
                    })
                    .unwrap_or_default();
                self.tree.imports.push(Import::C {
                    library,
                    functions,
                    errno,
                    threading,
                    decl,
                });
            }
            S::TypeDecl => self.push(ItemKind::Type, node, decl, whole()),
            S::FormDecl => {
                let before = self.tree.items.len();
                self.push(ItemKind::Form, node, decl, whole());
                if let Some(form) = self.tree.items.get(before).map(|i| i.id) {
                    let fns = node.children().filter(|n| n.kind() == S::FormFn);
                    for (index, slot) in fns.enumerate() {
                        let signature = slot.green().without_trivia();
                        if let Some(item) = self.item(ItemKind::Slot, &slot, false, decl, signature)
                        {
                            self.tree.slots.push(SlotItem {
                                id: item.id,
                                form,
                                index: index as u32,
                            });
                        }
                    }
                }
            }
            S::EmbedDecl => self.push(ItemKind::Embed, node, decl, whole()),
            S::FnDecl => {
                let signature = without(
                    node,
                    |e| matches!(e, GreenElement::Node(n) if n.kind() == S::Block),
                );
                self.push(ItemKind::Function, node, decl, signature);
            }
            S::LetDecl => {
                // Everything before the `=`: the pattern and the type.
                let mut seen_equals = false;
                let signature = without(node, |e| {
                    seen_equals |= matches!(e, GreenElement::Token(t)
                        if t.kind() == LeafKind::Token(T::Equals));
                    seen_equals
                });
                let mut names = Vec::new();
                if let Some(pattern) = node.children().next() {
                    bound_names(&pattern, &mut names);
                }
                for name in names {
                    let item =
                        self.item_named(ItemKind::Value, &name, false, decl, signature.clone());
                    self.tree.items.push(item);
                }
            }
            S::TestDecl => {
                if let Some(label) = node
                    .children()
                    .find(|n| matches!(n.kind(), S::Literal | S::StrExpr))
                {
                    let label = label.text();
                    let ordinal = self
                        .tree
                        .tests
                        .iter()
                        .filter(|t| *t.id.label(self.db) == label)
                        .count();
                    let id = TestId::new(self.db, self.module, label, ordinal as u32);
                    self.tree.tests.push(Test { id, decl });
                }
            }
            _ => {}
        }
    }

    fn import(&mut self, decl: u32, node: &SyntaxNode) -> Import<'db> {
        let path = node
            .children()
            .find(|n| n.kind() == S::Path)
            .map(|path| idents(&path).map(|n| self.name(&n)).collect())
            .unwrap_or_default();
        let alias = idents(node).next().map(|n| self.name(&n));
        let items = node
            .children()
            .find(|n| n.kind() == S::ImportItems)
            .map(|items| {
                items
                    .children()
                    .filter_map(|item| {
                        let mut names = idents(&item);
                        let name = self.name(&names.next()?);
                        let alias = names.next().map(|n| self.name(&n));
                        Some(ImportItem { name, alias })
                    })
                    .collect()
            });
        Import::Module {
            path,
            alias,
            items,
            decl,
        }
    }

    fn push(&mut self, kind: ItemKind, node: &SyntaxNode, decl: u32, signature: GreenNode) {
        let public = node.tokens().any(|t| t.kind() == LeafKind::Token(T::Pub));
        if let Some(item) = self.item(kind, node, public, decl, signature) {
            self.tree.items.push(item);
        }
    }

    /// An item named by the first identifier of `node`.
    fn item(
        &mut self,
        kind: ItemKind,
        node: &SyntaxNode,
        public: bool,
        decl: u32,
        signature: GreenNode,
    ) -> Option<Item<'db>> {
        let name = idents(node).next()?;
        Some(self.item_named(kind, &name, public, decl, signature))
    }

    fn item_named(
        &mut self,
        kind: ItemKind,
        name: &str,
        public: bool,
        decl: u32,
        signature: GreenNode,
    ) -> Item<'db> {
        let name = self.name(name);
        let ordinal = self.ordinals.entry((name, kind)).or_default();
        let id = ItemId::new(self.db, self.module, name, kind, *ordinal);
        *ordinal += 1;
        Item {
            id,
            public,
            decl,
            signature,
        }
    }

    fn name(&self, text: &str) -> Name<'db> {
        Name::new(self.db, text.to_string())
    }
}

/// The texts of the identifiers among the direct children of `node`.
fn idents(node: &SyntaxNode) -> impl Iterator<Item = String> + use<> {
    node.tokens()
        .filter(|t| t.kind() == LeafKind::Token(T::Ident))
        .map(|t| t.text().to_string())
}

/// `node` without the children `drop` picks and without trivia.
fn without(node: &SyntaxNode, mut drop: impl FnMut(&GreenElement) -> bool) -> GreenNode {
    let children = node
        .green()
        .children()
        .iter()
        .filter(|e| !drop(e))
        .cloned()
        .collect();
    GreenNode::new(node.kind(), children).without_trivia()
}

/// The names a `let` pattern may bind. A bare name binds unless a type of
/// that name is visible (§6.9), which only the module's scope knows, so
/// every bare name is listed here.
fn bound_names(pattern: &SyntaxNode, out: &mut Vec<String>) {
    let mut bindings = Vec::new();
    patterns::bindings(pattern, false, &mut bindings);
    out.extend(bindings.iter().map(|b| b.name().to_string()));
}
