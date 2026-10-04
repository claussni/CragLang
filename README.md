# Crag

Compiler, host and runtime for the Crag language, written in Rust.

- `docs/Specification.md` defines the language.
- `docs/Crag Compiler Architecture.md` records how the toolchain is built.
- `docs/Crag Implementation Plan.md` lists the milestones and components.

## Layout

| Crate | M0 component |
| --- | --- |
| `crates/crag-runtime` | Fiber runtime, stack growth, side stack, sentinel, stress harness |
| `crates/crag-codegen` | Cranelift facade |
| `crates/crag-loader` | Code loader |
| `crates/crag-db` | Salsa facade |
| `crates/crag-store` | Artifact store skeleton |

## Build

The toolchain is pinned in `Dockerfile` (Rust 1.99 with rustfmt and clippy).
The `./cargo` wrapper builds that image on first use and runs cargo inside it,
so only Docker is needed on the host.

    ./cargo build
    ./cargo test
    ./cargo clippy --all-targets
    ./cargo fmt
