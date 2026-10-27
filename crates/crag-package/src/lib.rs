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

//! Packages (Specification §14.5, §20.4 to §20.6): manifests, versions,
//! folder registries, resolution, package content and the SBOM.

pub mod content;
pub mod home;
pub mod manifest;
pub mod registry;
pub mod resolve;
pub mod sbom;
pub mod version;

pub use manifest::{Dependency, Manifest, ManifestError, Source};
pub use registry::Registry;
pub use resolve::{Origin, Resolution, Resolved, resolve};
pub use sbom::Sbom;
pub use version::Version;

/// The runtime version this tool provides; a package states the one it
/// requires (§14.5, rule 7).
pub const RUNTIME: Version = Version {
    major: 0,
    minor: 0,
    patch: None,
};
