FROM rust:slim

WORKDIR ~/scryer-prolog
COPY . .

RUN cargo --version
RUN cargo install --path .

CMD ["scryer-prolog"]
