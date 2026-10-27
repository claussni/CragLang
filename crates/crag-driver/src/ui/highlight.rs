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

//! Syntax highlighting (Specification §20.8.1) by the language's own lexer,
//! so it agrees with the compiler on every token, also in broken code: an
//! unclosed string is still a string, and keywords after `.` are fields.

use crag_syntax::{TokenKind, TriviaKind, lex};

/// What a piece of source is, for its colour.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Class {
    Keyword,
    /// A name that starts with a capital: types, forms and their cases.
    Type,
    /// A name being declared by `fn` or called.
    Function,
    Str,
    Number,
    Comment,
}

/// The classes of a text, by byte range, in order.
#[derive(Clone, Debug, Default)]
pub struct Highlights {
    spans: Vec<(u32, u32, Class)>,
}

impl Highlights {
    pub fn of(text: &str) -> Highlights {
        use TokenKind as T;
        let tokens = lex(text);
        let mut spans = Vec::new();
        for (i, token) in tokens.iter().enumerate() {
            for (kind, range) in token.trivia(text) {
                if matches!(kind, TriviaKind::LineComment | TriviaKind::BlockComment) {
                    spans.push((range.start as u32, range.end as u32, Class::Comment));
                }
            }
            let next = tokens.get(i + 1);
            let after_fn = i > 0 && tokens[i - 1].kind == T::Fn;
            let class = match token.kind {
                k if k.is_keyword() => Class::Keyword,
                T::Str
                | T::StrStart
                | T::TripleStrStart
                | T::StrMid
                | T::StrEnd
                | T::Bytes
                | T::CodePoint => Class::Str,
                T::Int | T::Float => Class::Number,
                T::Ident if token.text(text).starts_with(char::is_uppercase) => Class::Type,
                T::Ident
                    if after_fn
                        || next
                            .is_some_and(|n| n.kind == T::LParen && n.trivia_start == n.start) =>
                {
                    Class::Function
                }
                _ => continue,
            };
            spans.push((token.start, token.end, class));
        }
        Highlights { spans }
    }

    /// The class of the byte at `at`, if it has one.
    pub fn at(&self, at: usize) -> Option<Class> {
        let at = at as u32;
        let i = self.spans.partition_point(|&(_, end, _)| end <= at);
        self.spans
            .get(i)
            .filter(|&&(start, _, _)| start <= at)
            .map(|&(_, _, class)| class)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn classes(text: &str) -> Vec<(&str, Class)> {
        let h = Highlights::of(text);
        h.spans
            .iter()
            .map(|&(s, e, c)| (&text[s as usize..e as usize], c))
            .collect()
    }

    #[test]
    fn tokens_get_the_classes_of_their_kinds() {
        let text = "// area\npub fn area(p: Point) -> Int { p.type + 1.5 + f(\"a{x}b\") }\n";
        assert_eq!(
            classes(text),
            vec![
                ("// area", Class::Comment),
                ("pub", Class::Keyword),
                ("fn", Class::Keyword),
                ("area", Class::Function),
                ("Point", Class::Type),
                ("Int", Class::Type),
                ("1.5", Class::Number),
                ("f", Class::Function),
                ("\"a{", Class::Str),
                ("}b\"", Class::Str),
            ]
        );
        let h = Highlights::of(text);
        assert_eq!(h.at(0), Some(Class::Comment));
        assert_eq!(h.at(7), None);
        assert_eq!(h.at(text.find("Point").unwrap() + 2), Some(Class::Type));
    }

    #[test]
    fn an_unclosed_string_stays_a_string() {
        assert_eq!(
            classes("let s = \"open"),
            vec![("let", Class::Keyword), ("\"open", Class::Str)]
        );
    }
}
