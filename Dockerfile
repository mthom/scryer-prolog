# Based on https://blog.sedrik.se/posts/my-docker-setup-for-rust/
FROM ekidd/rust-musl-builder as builder

WORKDIR /home/rust/

# Install external dependencies
RUN sudo apt-get update
RUN sudo apt-get -y install m4

# Avoid having to install/build all dependencies by copying
# the Cargo files and making a dummy src/main.rs and build.rs
COPY Cargo.toml .
COPY Cargo.lock .
RUN echo "fn main() {}" > src/main.rs
RUN echo "fn main() {}" > build.rs
RUN cargo build --release

# We need to touch our real main.rs and build.rs files or else
# docker will use the cached one.
COPY . .
RUN sudo touch src/main.rs
RUN sudo touch build.rs

RUN cargo build --release

# Size optimization
# RUN strip target/x86_64-unknown-linux-musl/release/scryer-prolog

# Start building the final image
FROM scratch
WORKDIR /home/rust/
COPY --from=builder /home/rust/target/x86_64-unknown-linux-musl/release/scryer-prolog .
ENTRYPOINT ["./scryer-prolog"]
