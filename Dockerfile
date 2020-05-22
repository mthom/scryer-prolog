# Based on https://hub.docker.com/_/rust?tab=description and https://hub.docker.com/_/rust?tab=description

# The first container is for build purposes only.
FROM rust as builder

WORKDIR /usr/src/scryer-prolog

# Using a dummy build.rs and src/main.rs with your Cargo.toml lets Docker cache your Rust dependencies and not rebuild
# them every time.
COPY Cargo.toml .
COPY Cargo.lock .
RUN mkdir -p src
RUN echo "fn main() {}" > src/main.rs
RUN echo "fn main() {}" > build.rs
RUN cargo build --release

# We need to touch our real main.rs and build.rs files or else
# docker will use the cached ones.
COPY . .
RUN touch src/main.rs
RUN touch build.rs

RUN cargo build --release

RUN ls ./target/release

# Finally, copy the scryer-prolog executable to a slimmer container.
FROM debian:buster-slim
COPY --from=builder /usr/src/scryer-prolog/target/release/scryer-prolog /usr/local/bin/scryer-prolog
CMD ["scryer-prolog"]
