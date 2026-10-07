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

//! The red tree: a view of a green tree that adds parents and absolute
//! positions (Implementation Plan §11.4.2). Red nodes are made on demand
//! while walking and are cheap to clone; the green tree stays shared.

use std::ops::Range;
use std::rc::Rc;

use crate::green::{GreenElement, GreenNode, GreenToken};
use crate::kind::{LeafKind, SyntaxKind};

#[derive(Clone)]
pub struct SyntaxNode(Rc<NodeData>);

struct NodeData {
    green: GreenNode,
    parent: Option<SyntaxNode>,
    /// The node's index among its parent's children.
    index: usize,
    offset: u32,
}

#[derive(Clone)]
pub struct SyntaxToken {
    green: GreenToken,
    parent: SyntaxNode,
    index: usize,
    offset: u32,
}

#[derive(Clone, Debug)]
pub enum SyntaxElement {
    Node(SyntaxNode),
    Token(SyntaxToken),
}

impl SyntaxNode {
    pub fn new_root(green: GreenNode) -> SyntaxNode {
        SyntaxNode(Rc::new(NodeData {
            green,
            parent: None,
            index: 0,
            offset: 0,
        }))
    }

    pub fn kind(&self) -> SyntaxKind {
        self.0.green.kind()
    }

    pub fn green(&self) -> &GreenNode {
        &self.0.green
    }

    pub fn range(&self) -> Range<u32> {
        self.0.offset..self.0.offset + self.0.green.len()
    }

    pub fn text(&self) -> String {
        self.0.green.text()
    }

    pub fn parent(&self) -> Option<SyntaxNode> {
        self.0.parent.clone()
    }

    pub fn index(&self) -> usize {
        self.0.index
    }

    /// This node and its ancestors, innermost first.
    pub fn ancestors(&self) -> impl Iterator<Item = SyntaxNode> + use<> {
        std::iter::successors(Some(self.clone()), SyntaxNode::parent)
    }

    pub fn children_with_tokens(&self) -> impl Iterator<Item = SyntaxElement> + use<> {
        let parent = self.clone();
        let mut offset = self.0.offset;
        let green = self.0.green.clone();
        (0..green.children().len()).map(move |index| {
            let child = &green.children()[index];
            let element = match child {
                GreenElement::Node(node) => SyntaxElement::Node(SyntaxNode(Rc::new(NodeData {
                    green: node.clone(),
                    parent: Some(parent.clone()),
                    index,
                    offset,
                }))),
                GreenElement::Token(token) => SyntaxElement::Token(SyntaxToken {
                    green: token.clone(),
                    parent: parent.clone(),
                    index,
                    offset,
                }),
            };
            offset += child.len();
            element
        })
    }

    pub fn children(&self) -> impl Iterator<Item = SyntaxNode> + use<> {
        self.children_with_tokens().filter_map(|e| match e {
            SyntaxElement::Node(node) => Some(node),
            SyntaxElement::Token(_) => None,
        })
    }

    /// The tokens among the node's direct children, trivia included.
    pub fn tokens(&self) -> impl Iterator<Item = SyntaxToken> + use<> {
        self.children_with_tokens().filter_map(|e| match e {
            SyntaxElement::Token(token) => Some(token),
            SyntaxElement::Node(_) => None,
        })
    }

    /// This node and every node below it, in source order.
    pub fn descendants(&self) -> impl Iterator<Item = SyntaxNode> + use<> {
        let mut stack = vec![self.clone()];
        std::iter::from_fn(move || {
            let node = stack.pop()?;
            let children: Vec<_> = node.children().collect();
            stack.extend(children.into_iter().rev());
            Some(node)
        })
    }

    /// Every token below this node, in source order, trivia included.
    pub fn descendant_tokens(&self) -> impl Iterator<Item = SyntaxToken> + use<> {
        let mut stack = vec![SyntaxElement::Node(self.clone())];
        std::iter::from_fn(move || {
            loop {
                match stack.pop()? {
                    SyntaxElement::Token(token) => return Some(token),
                    SyntaxElement::Node(node) => {
                        let children: Vec<_> = node.children_with_tokens().collect();
                        stack.extend(children.into_iter().rev());
                    }
                }
            }
        })
    }

    /// The innermost token covering `offset`; at a boundary, the token that
    /// starts there.
    pub fn token_at(&self, offset: u32) -> Option<SyntaxToken> {
        let mut node = self.clone();
        loop {
            let child = node
                .children_with_tokens()
                .find(|c| c.range().start <= offset && offset < c.range().end)?;
            match child {
                SyntaxElement::Token(token) => return Some(token),
                SyntaxElement::Node(child) => node = child,
            }
        }
    }
}

impl SyntaxToken {
    pub fn kind(&self) -> LeafKind {
        self.green.kind()
    }

    pub fn text(&self) -> &str {
        self.green.text()
    }

    pub fn range(&self) -> Range<u32> {
        self.offset..self.offset + self.green.len()
    }

    pub fn parent(&self) -> SyntaxNode {
        self.parent.clone()
    }

    pub fn index(&self) -> usize {
        self.index
    }

    pub fn is_trivia(&self) -> bool {
        matches!(self.kind(), LeafKind::Trivia(_))
    }
}

impl SyntaxElement {
    pub fn range(&self) -> Range<u32> {
        match self {
            SyntaxElement::Node(node) => node.range(),
            SyntaxElement::Token(token) => token.range(),
        }
    }
}

impl PartialEq for SyntaxNode {
    /// The same node of the same tree.
    fn eq(&self, other: &SyntaxNode) -> bool {
        self.0.green == other.0.green && self.0.offset == other.0.offset
    }
}

impl Eq for SyntaxNode {}

impl std::fmt::Debug for SyntaxNode {
    /// One line per node and token, indented by depth; `{:#?}` shows the
    /// whole subtree, `{:?}` only this node.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !f.alternate() {
            return write!(f, "{:?}@{:?}", self.kind(), self.range());
        }
        fn go(
            node: &SyntaxNode,
            depth: usize,
            f: &mut std::fmt::Formatter<'_>,
        ) -> std::fmt::Result {
            writeln!(
                f,
                "{:indent$}{:?}@{:?}",
                "",
                node.kind(),
                node.range(),
                indent = depth * 2
            )?;
            for child in node.children_with_tokens() {
                match child {
                    SyntaxElement::Node(child) => go(&child, depth + 1, f)?,
                    SyntaxElement::Token(token) => {
                        writeln!(f, "{:indent$}{:?}", "", token, indent = depth * 2 + 2)?
                    }
                }
            }
            Ok(())
        }
        go(self, 0, f)
    }
}

impl std::fmt::Debug for SyntaxToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let kind = match self.kind() {
            LeafKind::Token(kind) => format!("{kind:?}"),
            LeafKind::Trivia(kind) => format!("{kind:?}"),
        };
        write!(f, "{kind}@{:?} {:?}", self.range(), self.text())
    }
}
