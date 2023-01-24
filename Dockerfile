# See https://github.com/LukeMathWalker/cargo-chef
ARG RUST_VERSION=1-buster
FROM rust:${RUST_VERSION} as planner
WORKDIR /scryer-prolog
RUN cargo install cargo-chef 
COPY . .
RUN cargo chef prepare --recipe-path recipe.json

FROM rust:${RUST_VERSION} as cacher
WORKDIR /scryer-prolog
RUN cargo install cargo-chef
COPY --from=planner /scryer-prolog/recipe.json recipe.json
RUN cargo chef cook --release --recipe-path recipe.json

FROM rust:${RUST_VERSION} as builder
WORKDIR /scryer-prolog
COPY . .
# Copy over the cached dependencies
COPY --from=cacher /scryer-prolog/target target
COPY --from=cacher $CARGO_HOME $CARGO_HOME
RUN cargo build --release --bin scryer-prolog

FROM debian:stable-slim
COPY --from=builder /scryer-prolog/target/release/scryer-prolog /usr/local/bin
ENV RUST_BACKTRACE=1
ENTRYPOINT ["/usr/local/bin/scryer-prolog"]
