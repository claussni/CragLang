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

//! Versions (Specification §14.5): a major and a minor version and an
//! optional patch level, written exactly as the manifest states them.

use std::cmp::Ordering;
use std::fmt;

/// A version such as `1.1` or `1.1.2`. A missing patch level counts as 0
/// when versions are compared, so `1.1` and `1.1.0` are the same version;
/// each is shown as it was written.
#[derive(Clone, Copy, Debug)]
pub struct Version {
    pub major: u32,
    pub minor: u32,
    pub patch: Option<u32>,
}

impl Version {
    pub fn new(major: u32, minor: u32, patch: Option<u32>) -> Version {
        Version {
            major,
            minor,
            patch,
        }
    }

    /// Reads `major.minor` or `major.minor.patch`, digits only.
    pub fn parse(text: &str) -> Result<Version, String> {
        let bad = || format!("`{text}` is not a version: write major.minor or major.minor.patch");
        let parts: Vec<&str> = text.split('.').collect();
        if !(2..=3).contains(&parts.len()) {
            return Err(bad());
        }
        let number = |part: &str| -> Result<u32, String> {
            if part.is_empty() || !part.bytes().all(|b| b.is_ascii_digit()) {
                return Err(bad());
            }
            // A leading zero would give one version two spellings.
            if part.len() > 1 && part.starts_with('0') {
                return Err(bad());
            }
            part.parse().map_err(|_| bad())
        };
        Ok(Version {
            major: number(parts[0])?,
            minor: number(parts[1])?,
            patch: parts.get(2).map(|p| number(p)).transpose()?,
        })
    }

    fn key(&self) -> (u32, u32, u32) {
        (self.major, self.minor, self.patch.unwrap_or(0))
    }

    /// Whether code written against `self` may run with `other`: the same
    /// major, and `other` no older.
    pub fn satisfied_by(&self, other: &Version) -> bool {
        self.major == other.major && other >= self
    }
}

impl PartialEq for Version {
    fn eq(&self, other: &Version) -> bool {
        self.key() == other.key()
    }
}

impl Eq for Version {}

impl std::hash::Hash for Version {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.key().hash(state);
    }
}

impl PartialOrd for Version {
    fn partial_cmp(&self, other: &Version) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Version {
    fn cmp(&self, other: &Version) -> Ordering {
        self.key().cmp(&other.key())
    }
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}", self.major, self.minor)?;
        if let Some(patch) = self.patch {
            write!(f, ".{patch}")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn versions_read_compare_and_show_as_written() {
        let v = |t| Version::parse(t).unwrap();
        assert_eq!(v("1.1"), v("1.1.0"));
        assert!(v("1.10") > v("1.9"));
        assert!(v("1.1.2") > v("1.1"));
        assert_eq!(v("1.1").to_string(), "1.1");
        assert_eq!(v("1.1.0").to_string(), "1.1.0");
        assert!(v("1.2").satisfied_by(&v("1.4.1")));
        assert!(!v("1.2").satisfied_by(&v("1.1")));
        assert!(!v("1.2").satisfied_by(&v("2.0")));
        for bad in ["1", "1.2.3.4", "a.1", "01.2", "1..2", "1.2-beta"] {
            assert!(Version::parse(bad).is_err(), "{bad}");
        }
    }
}
