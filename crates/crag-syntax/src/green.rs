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

//! The green tree: immutable, shareable nodes that know their kind, length
//! and children but not their position or parent (Implementation Plan
//! §11.4.2).
//!
//! Leaves hold their text, so a green tree is a complete, lossless copy of
//! the source. A `NodeCache` deduplicates while building: equal leaves are
//! one allocation, and so are equal small nodes, which are the bulk of a
//! tree (`x`, `1`, `a + b`).

use std::collections::HashMap;
use std::hash::{BuildHasher, Hash, RandomState};
use std::sync::Arc;

use crate::kind::{LeafKind, SyntaxKind};

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct GreenNode(Arc<NodeData>);

#[derive(PartialEq, Eq, Hash)]
struct NodeData {
    kind: SyntaxKind,
    len: u32,
    children: Box<[GreenElement]>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct GreenToken(Arc<TokenData>);

#[derive(PartialEq, Eq, Hash)]
struct TokenData {
    kind: LeafKind,
    text: Box<str>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum GreenElement {
    Node(GreenNode),
    Token(GreenToken),
}

impl GreenNode {
    pub fn kind(&self) -> SyntaxKind {
        self.0.kind
    }

    /// The length of the node's text in bytes.
    pub fn len(&self) -> u32 {
        self.0.len
    }

    pub fn is_empty(&self) -> bool {
        self.0.len == 0
    }

    pub fn children(&self) -> &[GreenElement] {
        &self.0.children
    }

    /// The source text the node covers.
    pub fn text(&self) -> String {
        let mut text = String::with_capacity(self.len() as usize);
        self.write_text(&mut text);
        text
    }

    fn write_text(&self, out: &mut String) {
        for child in self.children() {
            match child {
                GreenElement::Node(node) => node.write_text(out),
                GreenElement::Token(token) => out.push_str(token.text()),
            }
        }
    }

    fn addr(&self) -> usize {
        Arc::as_ptr(&self.0) as usize
    }
}

impl GreenToken {
    pub fn kind(&self) -> LeafKind {
        self.0.kind
    }

    pub fn text(&self) -> &str {
        &self.0.text
    }

    pub fn len(&self) -> u32 {
        self.0.text.len() as u32
    }

    pub fn is_empty(&self) -> bool {
        self.0.text.is_empty()
    }

    fn addr(&self) -> usize {
        Arc::as_ptr(&self.0) as usize
    }
}

impl GreenElement {
    pub fn len(&self) -> u32 {
        match self {
            GreenElement::Node(node) => node.len(),
            GreenElement::Token(token) => token.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Identity, which for deduplicated children is equality.
    fn addr(&self) -> usize {
        match self {
            GreenElement::Node(node) => node.addr(),
            GreenElement::Token(token) => token.addr(),
        }
    }
}

impl std::fmt::Debug for GreenNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}@{}", self.kind(), self.len())
    }
}

impl std::fmt::Debug for GreenToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} {:?}", self.kind(), self.text())
    }
}

impl std::fmt::Debug for GreenElement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GreenElement::Node(node) => node.fmt(f),
            GreenElement::Token(token) => token.fmt(f),
        }
    }
}

/// Nodes with more children than this are not deduplicated: large nodes
/// rarely repeat, and hashing them costs more than it saves.
const MAX_SHARED_CHILDREN: usize = 3;

/// Deduplicates leaves and small nodes. Since the children of a node were
/// deduplicated first, two small nodes are equal exactly when they have the
/// same kind and the same child allocations, so a node is looked up by its
/// children's addresses without walking them.
#[derive(Default)]
pub struct NodeCache {
    hasher: RandomState,
    tokens: HashMap<u64, Vec<GreenToken>>,
    nodes: HashMap<u64, Vec<GreenNode>>,
}

impl NodeCache {
    pub fn token(&mut self, kind: LeafKind, text: &str) -> GreenToken {
        let hash = self.hasher.hash_one((kind, text));
        let bucket = self.tokens.entry(hash).or_default();
        if let Some(token) = bucket.iter().find(|t| t.kind() == kind && t.text() == text) {
            return token.clone();
        }
        let token = GreenToken(Arc::new(TokenData {
            kind,
            text: text.into(),
        }));
        bucket.push(token.clone());
        token
    }

    pub fn node(&mut self, kind: SyntaxKind, children: Vec<GreenElement>) -> GreenNode {
        let make = |children: Vec<GreenElement>| {
            GreenNode(Arc::new(NodeData {
                kind,
                len: children.iter().map(GreenElement::len).sum(),
                children: children.into(),
            }))
        };
        if children.len() > MAX_SHARED_CHILDREN {
            return make(children);
        }
        let mut hasher = self.hasher.build_hasher();
        kind.hash(&mut hasher);
        for child in &children {
            child.addr().hash(&mut hasher);
        }
        let hash = std::hash::Hasher::finish(&hasher);
        let bucket = self.nodes.entry(hash).or_default();
        let same = |node: &&GreenNode| {
            node.kind() == kind
                && node.children().len() == children.len()
                && node
                    .children()
                    .iter()
                    .zip(&children)
                    .all(|(a, b)| a.addr() == b.addr())
        };
        if let Some(node) = bucket.iter().find(same) {
            return node.clone();
        }
        let node = make(children);
        bucket.push(node.clone());
        node
    }
}

/// Builds a green tree from a sequence of start, leaf and finish calls.
pub struct Builder {
    cache: NodeCache,
    /// The open nodes, each with the index of its first child in `children`.
    parents: Vec<(SyntaxKind, usize)>,
    children: Vec<GreenElement>,
}

/// A position among the children of the open node, at which a node can be
/// started later, wrapping everything added since.
#[derive(Clone, Copy)]
pub struct Checkpoint(usize);

impl Builder {
    pub fn new(cache: NodeCache) -> Builder {
        Builder {
            cache,
            parents: Vec::new(),
            children: Vec::new(),
        }
    }

    pub fn start_node(&mut self, kind: SyntaxKind) {
        self.parents.push((kind, self.children.len()));
    }

    pub fn checkpoint(&self) -> Checkpoint {
        Checkpoint(self.children.len())
    }

    /// Starts a node whose first child is the one added at `checkpoint`.
    pub fn start_node_at(&mut self, checkpoint: Checkpoint, kind: SyntaxKind) {
        let first = self.parents.last().map_or(0, |&(_, first)| first);
        assert!(
            first <= checkpoint.0 && checkpoint.0 <= self.children.len(),
            "checkpoint outside the open node"
        );
        self.parents.push((kind, checkpoint.0));
    }

    pub fn leaf(&mut self, kind: LeafKind, text: &str) {
        let token = self.cache.token(kind, text);
        self.children.push(GreenElement::Token(token));
    }

    pub fn finish_node(&mut self) {
        let (kind, first) = self.parents.pop().expect("no open node");
        let children = self.children.split_off(first);
        let node = self.cache.node(kind, children);
        self.children.push(GreenElement::Node(node));
    }

    /// The finished tree. Exactly one node must have been built at the top.
    pub fn finish(mut self) -> (GreenNode, NodeCache) {
        assert!(self.parents.is_empty(), "unfinished nodes");
        assert_eq!(self.children.len(), 1, "one root expected");
        match self.children.pop() {
            Some(GreenElement::Node(root)) => (root, self.cache),
            _ => panic!("the root is not a node"),
        }
    }
}
