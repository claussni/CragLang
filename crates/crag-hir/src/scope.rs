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

//! Module scopes and imports (Implementation Plan §11.4.5).
//!
//! A module's scope holds its own items and the public items of the
//! modules it imports, with the prelude imported into every module but
//! itself (§19.3). Imports are not passed on, so a scope is made from item
//! trees alone: its own and those of the modules it imports. Only the
//! imported modules' types are needed one step further, to tell which bare
//! names in their `let` patterns bind (§6.9).
//!
//! When names meet, indistinguishable types merge, functions form one
//! overload set, and any other pair is a collision (§14.3). A binding may
//! share a name with functions (§5.4).

use std::collections::{HashMap, HashSet};

use crag_db::Db;
use crag_syntax::{GreenNode, LeafKind, SyntaxKind as S, SyntaxNode, TokenKind as T};

use crate::input::{ModuleId, Program};
use crate::items::{Import, Item, ItemId, ItemKind, ItemTree, Name, item_tree};
use crate::patterns;

/// The module imported into every other one (§19.3).
pub const PRELUDE: &str = "std.core";

/// The modules of a program by path, and the directories the paths imply.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ModuleIndex {
    pub modules: HashMap<String, ModuleId>,
    /// Every proper prefix of a module path: `a` and `a.b` for `a.b.c`.
    pub directories: HashSet<String>,
}

#[crag_db::tracked(returns(ref))]
pub fn module_index(db: &dyn Db, program: Program) -> ModuleIndex {
    let mut index = ModuleIndex::default();
    for &module in program.modules(db) {
        let path = module.path(db);
        index.modules.entry(path.clone()).or_insert(module);
        let mut prefix = path.as_str();
        while let Some(dot) = prefix.rfind('.') {
            prefix = &prefix[..dot];
            index.directories.insert(prefix.to_string());
        }
    }
    index
}

/// What an import path names (§14.1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PathTarget<'db> {
    Directory(String),
    Module(ModuleId),
    /// An element of a module: everything the module declares by that
    /// name.
    Element(ModuleId, Name<'db>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PathError {
    /// No module or directory has this path.
    Unknown(String),
    /// The path goes on after an element of a module.
    PastElement(String),
}

/// Resolves a dotted import path from the left: directories lead to the
/// first segment that names a module, and a segment after that names one
/// of its elements (§14.1).
pub fn resolve_path<'db>(
    db: &'db dyn Db,
    index: &ModuleIndex,
    path: &[Name<'db>],
) -> Result<PathTarget<'db>, PathError> {
    let mut prefix = String::new();
    for (i, segment) in path.iter().enumerate() {
        if i > 0 {
            prefix.push('.');
        }
        prefix.push_str(segment.text(db));
        if let Some(&module) = index.modules.get(&prefix) {
            return match &path[i + 1..] {
                [] => Ok(PathTarget::Module(module)),
                &[element] => Ok(PathTarget::Element(module, element)),
                _ => Err(PathError::PastElement(join(db, path))),
            };
        }
        if !index.directories.contains(&prefix) {
            return Err(PathError::Unknown(prefix));
        }
    }
    Ok(PathTarget::Directory(prefix))
}

fn join(db: &dyn Db, path: &[Name]) -> String {
    let segments: Vec<&str> = path.iter().map(|n| n.text(db).as_str()).collect();
    segments.join(".")
}

/// Where a name in a scope comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum Origin {
    Declared,
    /// The import at this index among the module's declarations.
    Imported(u32),
    Prelude,
}

/// One module an import brings names from.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct ImportTarget<'db> {
    pub origin: Origin,
    pub module: ModuleId,
    pub selection: Selection<'db>,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum Selection<'db> {
    /// Every public element.
    All,
    /// Elements by name, each with the name it is known by here.
    Elements(Vec<(Name<'db>, Name<'db>)>),
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum NameError<'db> {
    Path {
        decl: u32,
        error: PathError,
    },
    /// `as` on a module or a directory: only elements are renamed (§14.2).
    ModuleRenamed {
        decl: u32,
        path: String,
    },
    UnknownElement {
        decl: u32,
        module: ModuleId,
        name: Name<'db>,
    },
    /// The module has the element, but not `pub`.
    PrivateElement {
        decl: u32,
        module: ModuleId,
        name: Name<'db>,
    },
    /// A module file beside a directory of the same name (§14.1).
    ModuleBesideDirectory {
        path: String,
    },
    /// Items that may not share the name they have in this scope (§5.4,
    /// §14.3).
    Collision {
        name: Name<'db>,
        items: Vec<(ItemId<'db>, Origin)>,
    },
}

/// The modules a module imports from.
#[derive(Clone, Debug, Default, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Imports<'db> {
    pub targets: Vec<ImportTarget<'db>>,
    pub errors: Vec<NameError<'db>>,
}

/// Resolves the paths of a module's imports, the prelude first.
#[crag_db::tracked(returns(ref))]
pub fn imports<'db>(db: &'db dyn Db, program: Program, module: ModuleId) -> Imports<'db> {
    let index = module_index(db, program);
    let mut imports = Imports::default();
    if module.path(db) != PRELUDE
        && let Some(&prelude) = index.modules.get(PRELUDE)
    {
        imports.targets.push(ImportTarget {
            origin: Origin::Prelude,
            module: prelude,
            selection: Selection::All,
        });
    }
    for import in &item_tree(db, module).imports {
        let Import::Module {
            path,
            alias,
            items,
            decl,
        } = import
        else {
            continue;
        };
        // An empty path was reported by the parser.
        if !path.is_empty()
            && let Err(error) = import_targets(db, index, *decl, path, *alias, items, &mut imports)
        {
            imports.errors.push(error);
        }
    }
    imports
}

fn import_targets<'db>(
    db: &'db dyn Db,
    index: &ModuleIndex,
    decl: u32,
    path: &[Name<'db>],
    alias: Option<Name<'db>>,
    items: &Option<Vec<crate::items::ImportItem<'db>>>,
    imports: &mut Imports<'db>,
) -> Result<(), NameError<'db>> {
    let target = resolve_path(db, index, path).map_err(|error| NameError::Path { decl, error })?;
    let renamed = || NameError::ModuleRenamed {
        decl,
        path: join(db, path),
    };
    let origin = Origin::Imported(decl);
    let mut push = |module, selection| {
        imports.targets.push(ImportTarget {
            origin,
            module,
            selection,
        })
    };
    match target {
        PathTarget::Module(module) => {
            if alias.is_some() {
                return Err(renamed());
            }
            let selection = match items {
                None => Selection::All,
                Some(items) => Selection::Elements(
                    items
                        .iter()
                        .map(|i| (i.name, i.alias.unwrap_or(i.name)))
                        .collect(),
                ),
            };
            push(module, selection);
        }
        PathTarget::Element(module, element) => {
            if items.is_some() {
                return Err(NameError::Path {
                    decl,
                    error: PathError::PastElement(join(db, path)),
                });
            }
            push(
                module,
                Selection::Elements(vec![(element, alias.unwrap_or(element))]),
            );
        }
        PathTarget::Directory(directory) => {
            if alias.is_some() {
                return Err(renamed());
            }
            match items {
                // The modules directly in the directory, not those below.
                None => {
                    let mut modules: Vec<(&String, ModuleId)> = index
                        .modules
                        .iter()
                        .filter(|(p, _)| {
                            p.strip_prefix(&directory)
                                .and_then(|rest| rest.strip_prefix('.'))
                                .is_some_and(|rest| !rest.contains('.'))
                        })
                        .map(|(p, &m)| (p, m))
                        .collect();
                    modules.sort_by_key(|&(p, _)| p);
                    for (_, module) in modules {
                        push(module, Selection::All);
                    }
                }
                Some(items) => {
                    for item in items {
                        let path = format!("{directory}.{}", item.name.text(db));
                        if item.alias.is_some() {
                            imports.errors.push(NameError::ModuleRenamed { decl, path });
                        } else if let Some(&module) = index.modules.get(&path) {
                            imports.targets.push(ImportTarget {
                                origin,
                                module,
                                selection: Selection::All,
                            });
                        } else {
                            imports.errors.push(NameError::Path {
                                decl,
                                error: PathError::Unknown(path),
                            });
                        }
                    }
                }
            }
        }
    }
    Ok(())
}

/// A candidate for a name in a scope, before the names meet.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Entry<'db> {
    /// The name in this scope, which a rename makes differ from the
    /// item's.
    pub name: Name<'db>,
    pub item: Item<'db>,
    pub origin: Origin,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Entries<'db> {
    pub entries: Vec<Entry<'db>>,
    pub errors: Vec<NameError<'db>>,
}

/// Everything that enters a module's scope, own items first: what the
/// module declares, and the public items its imports select.
#[crag_db::tracked(returns(ref))]
pub fn scope_entries<'db>(db: &'db dyn Db, program: Program, module: ModuleId) -> Entries<'db> {
    let imports = imports(db, program, module);
    let mut result = Entries {
        entries: Vec::new(),
        errors: imports.errors.clone(),
    };
    for item in own_items(item_tree(db, module)) {
        result.entries.push(Entry {
            name: *item.id.name(db),
            item: item.clone(),
            origin: Origin::Declared,
        });
    }
    for target in &imports.targets {
        let tree = item_tree(db, target.module);
        let mut enter = |name, item: &Item<'db>| {
            result.entries.push(Entry {
                name,
                item: item.clone(),
                origin: target.origin,
            })
        };
        match &target.selection {
            Selection::All => {
                for item in tree.items.iter().filter(|i| i.public) {
                    enter(*item.id.name(db), item);
                }
            }
            Selection::Elements(elements) => {
                for &(element, name) in elements {
                    let named: Vec<&Item> = tree
                        .items
                        .iter()
                        .filter(|i| *i.id.name(db) == element)
                        .collect();
                    let Origin::Imported(decl) = target.origin else {
                        unreachable!("the prelude selects every element");
                    };
                    if named.is_empty() {
                        result.errors.push(NameError::UnknownElement {
                            decl,
                            module: target.module,
                            name: element,
                        });
                    } else if !named.iter().any(|i| i.public) {
                        result.errors.push(NameError::PrivateElement {
                            decl,
                            module: target.module,
                            name: element,
                        });
                    }
                    for item in named.into_iter().filter(|i| i.public) {
                        enter(name, item);
                    }
                }
            }
        }
    }
    result
}

/// A module's items, its C functions included.
fn own_items<'a, 'db>(tree: &'a ItemTree<'db>) -> impl Iterator<Item = &'a Item<'db>> {
    let c_functions = tree.imports.iter().flat_map(|import| match import {
        Import::C { functions, .. } => functions.as_slice(),
        Import::Module { .. } => &[],
    });
    tree.items.iter().chain(c_functions)
}

/// The names of the types visible in a module, which decide what the bare
/// names in its `let` patterns are.
#[crag_db::tracked(returns(ref))]
pub fn type_names<'db>(db: &'db dyn Db, program: Program, module: ModuleId) -> Vec<Name<'db>> {
    let mut names = Vec::new();
    for entry in &scope_entries(db, program, module).entries {
        if *entry.item.id.kind(db) == ItemKind::Type && !names.contains(&entry.name) {
            names.push(entry.name);
        }
    }
    names
}

/// What a name in a module's scope refers to.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum Resolution<'db> {
    /// A type. Indistinguishable types from several modules are one; the
    /// first stands for all.
    Type(ItemId<'db>),
    Form(ItemId<'db>),
    /// A value, an overload set of functions, or both (§5.4). The
    /// functions may come from several modules.
    Value {
        value: Option<ItemId<'db>>,
        functions: Vec<ItemId<'db>>,
    },
}

/// A module's scope, and what went wrong making it.
#[derive(Clone, Debug, Default, PartialEq, Eq, crag_db::SalsaValue)]
pub struct ModuleScope<'db> {
    pub names: HashMap<Name<'db>, Resolution<'db>>,
    pub errors: Vec<NameError<'db>>,
}

impl<'db> ModuleScope<'db> {
    pub fn resolve(&self, name: Name<'db>) -> Option<&Resolution<'db>> {
        self.names.get(&name)
    }

    /// Whether `name` is a type here, which makes a bare name in a pattern
    /// a type pattern (§6.9).
    pub fn is_type(&self, name: Name<'db>) -> bool {
        matches!(self.resolve(name), Some(Resolution::Type(_)))
    }
}

#[crag_db::tracked(returns(ref))]
pub fn module_scope<'db>(db: &'db dyn Db, program: Program, module: ModuleId) -> ModuleScope<'db> {
    let entries = scope_entries(db, program, module);
    let mut scope = ModuleScope {
        names: HashMap::new(),
        errors: entries.errors.clone(),
    };
    if module_index(db, program)
        .directories
        .contains(module.path(db))
    {
        scope.errors.push(NameError::ModuleBesideDirectory {
            path: module.path(db).clone(),
        });
    }
    // The names in order of first appearance, each with its distinct items.
    let mut order: Vec<Name> = Vec::new();
    let mut groups: HashMap<Name, Vec<&Entry>> = HashMap::new();
    for entry in &entries.entries {
        if binds_no_type(db, program, entry) {
            continue;
        }
        let group = groups.entry(entry.name).or_insert_with(|| {
            order.push(entry.name);
            Vec::new()
        });
        if group.iter().all(|e| e.item.id != entry.item.id) {
            group.push(entry);
        }
    }
    for name in order {
        let group = &groups[&name];
        let (resolution, collisions) = meet(db, group);
        for items in collisions {
            scope.errors.push(NameError::Collision {
                name,
                items: items.iter().map(|e| (e.item.id, e.origin)).collect(),
            });
        }
        scope.names.insert(name, resolution);
    }
    scope
}

/// Whether the entry is a `let` name that is a type pattern instead,
/// because a type of that name is visible where the `let` is.
fn binds_no_type(db: &dyn Db, program: Program, entry: &Entry) -> bool {
    let id = entry.item.id;
    if *id.kind(db) != ItemKind::Value || !maybe_type(&entry.item.signature, id.name(db).text(db)) {
        return false;
    }
    type_names(db, program, *id.module(db)).contains(id.name(db))
}

/// Whether every place `name` has in the pattern of a `let` signature is a
/// bare name, which a visible type makes a type pattern.
fn maybe_type(signature: &GreenNode, name: &str) -> bool {
    let root = SyntaxNode::new_root(signature.clone());
    let Some(pattern) = root.children().next() else {
        return false;
    };
    let mut bindings = Vec::new();
    patterns::bindings(&pattern, false, &mut bindings);
    bindings
        .iter()
        .filter(|b| b.name() == name)
        .all(|b| b.maybe_type)
}

/// How the items of one name meet: what the name resolves to, and the
/// groups of items that collide.
fn meet<'a, 'db>(
    db: &'db dyn Db,
    group: &[&'a Entry<'db>],
) -> (Resolution<'db>, Vec<Vec<&'a Entry<'db>>>) {
    let of = |kinds: &[ItemKind]| -> Vec<&'a Entry<'db>> {
        group
            .iter()
            .copied()
            .filter(|e| kinds.contains(e.item.id.kind(db)))
            .collect()
    };
    let types = of(&[ItemKind::Type]);
    let forms = of(&[ItemKind::Form]);
    let values = of(&[ItemKind::Value, ItemKind::Embed]);
    let functions = of(&[ItemKind::Function]);

    let resolution = if let Some(ty) = types.first() {
        Resolution::Type(ty.item.id)
    } else if let Some(form) = forms.first() {
        Resolution::Form(form.item.id)
    } else {
        Resolution::Value {
            value: values.first().map(|e| e.item.id),
            functions: functions.iter().map(|e| e.item.id).collect(),
        }
    };

    let kinds = [
        &types,
        &forms,
        &values.iter().chain(&functions).copied().collect(),
    ]
    .iter()
    .filter(|k| !k.is_empty())
    .count();
    if kinds > 1 {
        return (resolution, vec![group.to_vec()]);
    }
    let mut collisions = Vec::new();
    let merge = types
        .first()
        .and_then(|first| type_shape(&first.item.signature));
    if types.len() > 1
        && types
            .iter()
            .any(|t| merge.is_none() || type_shape(&t.item.signature) != merge)
    {
        collisions.push(types);
    }
    for same in [forms, values] {
        if same.len() > 1 {
            collisions.push(same);
        }
    }
    // Overloads with one signature clash (§14.3).
    let mut shapes: Vec<(FnShape, Vec<&Entry>)> = Vec::new();
    for function in functions {
        let shape = fn_shape(&function.item.signature);
        match shapes.iter_mut().find(|(s, _)| *s == shape) {
            Some((_, same)) => same.push(function),
            None => shapes.push((shape, vec![function])),
        }
    }
    collisions.extend(
        shapes
            .into_iter()
            .map(|(_, same)| same)
            .filter(|same| same.len() > 1),
    );
    (resolution, collisions)
}

/// The declaration that stands for a type's identity, name plus shape
/// (§3.3): of the declarations in the program that merge with it, the one
/// in the first module by path. A `distinct` or `opaque` type stands for
/// itself.
#[crag_db::tracked(returns(copy))]
pub fn type_identity<'db>(db: &'db dyn Db, program: Program, item: ItemId<'db>) -> ItemId<'db> {
    let tree = item_tree(db, *item.module(db));
    let Some(shape) = tree
        .items
        .iter()
        .find(|i| i.id == item)
        .and_then(|i| type_shape(&i.signature))
    else {
        return item;
    };
    let key = |id: ItemId<'db>| (id.module(db).path(db).clone(), *id.ordinal(db));
    let mut identity = item;
    for module in module_index(db, program).modules.values() {
        for other in &item_tree(db, *module).items {
            let id = other.id;
            if *id.kind(db) == ItemKind::Type
                && id.name(db) == item.name(db)
                && key(id) < key(identity)
                && type_shape(&other.signature).as_ref() == Some(&shape)
            {
                identity = id;
            }
        }
    }
    identity
}

/// A type declaration as compared for merging: without `pub`, and none
/// for `distinct` and `opaque` types, which never merge (§14.3).
fn type_shape(signature: &GreenNode) -> Option<Vec<crag_syntax::GreenElement>> {
    let token = |kind| move |e: &&crag_syntax::GreenElement| matches!(e, crag_syntax::GreenElement::Token(t) if t.kind() == LeafKind::Token(kind));
    let children = signature.children();
    if children
        .iter()
        .any(|e| token(T::Distinct)(&e) || token(T::Opaque)(&e))
    {
        return None;
    }
    Some(
        children
            .iter()
            .filter(|e| !token(T::Pub)(e))
            .cloned()
            .collect(),
    )
}

/// A function signature as compared for clashes: its type parameters, the
/// types of its parameters, its result type and its `where` clause, but
/// not its name, its parameters' names or `pub`.
#[derive(PartialEq, Eq)]
struct FnShape {
    type_params: Option<GreenNode>,
    params: Vec<Option<GreenNode>>,
    result: Option<GreenNode>,
    where_clause: Option<GreenNode>,
}

fn fn_shape(signature: &GreenNode) -> FnShape {
    let root = SyntaxNode::new_root(signature.clone());
    let child = |kind| root.children().find(|n| n.kind() == kind);
    let first_child = |node: SyntaxNode| node.children().next().map(|n| n.green().clone());
    let params = child(S::ParamList)
        .map(|list| {
            list.children()
                .filter(|n| n.kind() == S::Param)
                .map(first_child)
                .collect()
        })
        .unwrap_or_default();
    // A C signature has its result type right after the parameters.
    let result = match root.kind() {
        S::CSig => root
            .children()
            .skip_while(|n| n.kind() != S::ParamList)
            .nth(1)
            .map(|n| n.green().clone()),
        _ => child(S::ReturnType).and_then(first_child),
    };
    FnShape {
        type_params: child(S::TypeParams).map(|n| n.green().clone()),
        params,
        result,
        where_clause: child(S::WhereClause).map(|n| n.green().clone()),
    }
}

/// Which module imports which, and the cycles among them (§14.1).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ImportGraph {
    /// For every module, the modules it imports, each once.
    pub edges: HashMap<ModuleId, Vec<ModuleId>>,
    pub cycles: Vec<ImportCycle>,
}

/// A cycle of imports: each module imports the next, and the last the
/// first, each through the import at the declaration index given (none for
/// the prelude).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportCycle {
    pub steps: Vec<(ModuleId, Option<u32>)>,
}

/// The import graph, with one cycle reported for every group of modules
/// that import each other.
#[crag_db::tracked(returns(ref))]
pub fn import_graph(db: &dyn Db, program: Program) -> ImportGraph {
    let index = module_index(db, program);
    let modules: Vec<ModuleId> = program
        .modules(db)
        .iter()
        .copied()
        .filter(|m| index.modules.get(m.path(db)) == Some(m))
        .collect();
    let mut graph = ImportGraph::default();
    let mut steps: HashMap<(ModuleId, ModuleId), Option<u32>> = HashMap::new();
    for &module in &modules {
        let mut targets = Vec::new();
        for target in &imports(db, program, module).targets {
            let decl = match target.origin {
                Origin::Imported(decl) => Some(decl),
                _ => None,
            };
            if !targets.contains(&target.module) {
                targets.push(target.module);
                steps.insert((module, target.module), decl);
            }
        }
        graph.edges.insert(module, targets);
    }
    for component in strongly_connected(&modules, &graph.edges) {
        let start = component[0];
        let looped = component.len() > 1 || graph.edges[&start].contains(&start);
        if looped {
            let path = shortest_cycle(start, &component, &graph.edges);
            let steps = path
                .windows(2)
                .map(|w| (w[0], steps[&(w[0], w[1])]))
                .collect();
            graph.cycles.push(ImportCycle { steps });
        }
    }
    graph
}

/// Tarjan's algorithm. Each component lists its modules in the order of
/// `modules`, and the components come in the order of their first module.
fn strongly_connected(
    modules: &[ModuleId],
    edges: &HashMap<ModuleId, Vec<ModuleId>>,
) -> Vec<Vec<ModuleId>> {
    struct State<'a> {
        edges: &'a HashMap<ModuleId, Vec<ModuleId>>,
        index: HashMap<ModuleId, usize>,
        low: HashMap<ModuleId, usize>,
        stack: Vec<ModuleId>,
        on_stack: HashSet<ModuleId>,
        components: Vec<Vec<ModuleId>>,
    }
    fn visit(s: &mut State, module: ModuleId) {
        let n = s.index.len();
        s.index.insert(module, n);
        s.low.insert(module, n);
        s.stack.push(module);
        s.on_stack.insert(module);
        for &next in &s.edges[&module] {
            if !s.index.contains_key(&next) {
                visit(s, next);
                let low = s.low[&module].min(s.low[&next]);
                s.low.insert(module, low);
            } else if s.on_stack.contains(&next) {
                let low = s.low[&module].min(s.index[&next]);
                s.low.insert(module, low);
            }
        }
        if s.low[&module] == s.index[&module] {
            let mut component = Vec::new();
            while let Some(top) = s.stack.pop() {
                s.on_stack.remove(&top);
                component.push(top);
                if top == module {
                    break;
                }
            }
            s.components.push(component);
        }
    }
    let mut state = State {
        edges,
        index: HashMap::new(),
        low: HashMap::new(),
        stack: Vec::new(),
        on_stack: HashSet::new(),
        components: Vec::new(),
    };
    for &module in modules {
        if !state.index.contains_key(&module) {
            visit(&mut state, module);
        }
    }
    let position: HashMap<ModuleId, usize> =
        modules.iter().enumerate().map(|(i, &m)| (m, i)).collect();
    let mut components = state.components;
    for component in &mut components {
        component.sort_by_key(|m| position[m]);
    }
    components.sort_by_key(|c| position[&c[0]]);
    components
}

/// The shortest path from `start` back to itself within `component`, with
/// `start` at both ends.
fn shortest_cycle(
    start: ModuleId,
    component: &[ModuleId],
    edges: &HashMap<ModuleId, Vec<ModuleId>>,
) -> Vec<ModuleId> {
    let mut parent: HashMap<ModuleId, ModuleId> = HashMap::new();
    let mut queue = std::collections::VecDeque::from([start]);
    while let Some(module) = queue.pop_front() {
        for &next in &edges[&module] {
            if next == start {
                let mut path = vec![start, module];
                let mut at = module;
                while at != start {
                    at = parent[&at];
                    path.push(at);
                }
                path.reverse();
                return path;
            }
            if component.contains(&next) && !parent.contains_key(&next) {
                parent.insert(next, module);
                queue.push_back(next);
            }
        }
    }
    unreachable!("a component with a cycle through its first module")
}
