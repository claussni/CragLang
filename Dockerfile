# Development toolchain for Crag. Use it through ./cargo, which builds this
# image on first use and runs cargo inside it against the working tree.
FROM rust:1.99-bookworm
RUN rustup component add rustfmt clippy
