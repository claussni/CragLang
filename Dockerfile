# Development toolchain for Crag. Use it through ./cargo, which builds this
# image on first use and runs cargo inside it against the working tree.
# The musl target builds the runtime archive release executables link
# against, with the C library and start files it ships (Implementation
# Plan §11.10.4).
FROM docker.io/library/rust:1.99-bookworm
RUN rustup component add rustfmt clippy && rustup target add x86_64-unknown-linux-musl
# LMDB (crag-dur, Implementation Plan §11.11.2) is C, so the runtime
# archive's musl build needs a musl C compiler.
RUN apt-get update && apt-get install -y --no-install-recommends musl-tools \
    && rm -rf /var/lib/apt/lists/*
ENV CC_x86_64_unknown_linux_musl=musl-gcc
