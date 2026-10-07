# Crag

Compiler, host and runtime for the Crag language, written in Rust.

- `docs/Specification.md` defines the language.
- `docs/Crag Compiler Architecture.md` records how the toolchain is built.
- `docs/Crag Implementation Plan.md` lists the milestones and components.

## Layout

| Crate | Components |
| --- | --- |
| `crates/crag-runtime` | Fiber runtime, stack growth, side stack, sentinel, stress harness |
| `crates/crag-abi` | Constants shared by generated code and the runtime |
| `crates/crag-codegen` | Cranelift facade |
| `crates/crag-loader` | Code loader |
| `crates/crag-db` | Salsa facade |
| `crates/crag-store` | Artifact store skeleton |
| `crates/crag-syntax` | Lexer, parser and syntax tree (M1) |
| `crates/crag-hir` | Item trees, and later names and HIR (M1) |

## Build

The toolchain is pinned in `Dockerfile` (Rust 1.99 with rustfmt and clippy).
The `./cargo` wrapper builds that image on first use and runs cargo inside it,
so only Docker is needed on the host.

    ./cargo build
    ./cargo test
    ./cargo clippy --all-targets
    ./cargo fmt

## Use of Claude Code

Crag is designed and implemented with the help of
[Claude Code](https://claude.com/claude-code), Anthropic's coding agent. This
covers the documents in `docs/` as well as the code in `crates/`. Ralf
Claussnitzer directs the work, reviews the results and is responsible for
them.

## License

Copyright (C) 2026 Ralf Claussnitzer

Crag is free software: you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version. Crag is distributed without any warranty. See [LICENSE](LICENSE) for
the full text.
