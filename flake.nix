{
  description = "A modern Prolog implementation written mostly in Rust";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { nixpkgs, flake-utils, rust-overlay, ... }:
    let 
      meta = (builtins.fromTOML (builtins.readFile ./Cargo.toml)).package;
      inherit (meta) name version;
      overlays = [ 
        (import rust-overlay)
        (self: super: {
          rustToolchainDev = super.rust-bin.stable.latest.default.override {
            extensions = [ "rust-src" "rust-analyzer" ];
          };
          rustToolchainDevWasm = super.rust-bin.stable.latest.default.override {
            extensions = [ "rust-src" "rust-analyzer" ];
            targets = [ "wasm32-unknown-unknown" ];
          };
          rustToolchainNightly = super.rust-bin.selectLatestNightlyWith (toolchain:
            toolchain.default.override {
              extensions = [ "rust-src" "rust-analyzer" "miri" ];
            }
          );
        })
      ];
    in flake-utils.lib.eachDefaultSystem(system:
      let 
        pkgs = import nixpkgs { inherit system overlays; };
        nativeBuildInputs = with pkgs; [ pkg-config ];
        buildInputs = with pkgs; [ openssl ] ++
                                 lib.optionals pkgs.stdenv.isDarwin [
                                   pkgs.darwin.apple_sdk.frameworks.SystemConfiguration
                                 ];
      in
      {
        devShells = {
          default = pkgs.mkShell.override { stdenv = pkgs.clangMultiStdenv; } {
            nativeBuildInputs = nativeBuildInputs;
            buildInputs = buildInputs ++ (with pkgs; [
              rustToolchainDev
            ]);
          };
          wasm-js = pkgs.mkShell.override { stdenv = pkgs.clangMultiStdenv; } {
            nativeBuildInputs = nativeBuildInputs;
            buildInputs = buildInputs ++ (with pkgs; [
              wasm-pack
              rustToolchainDevWasm
            ]);
            TARGET_CC = "${pkgs.clangMultiStdenv.cc}/bin/clang";
            hardeningDisable = [ "all" ];
          };
          # For use with Miri and stuff like it
          nightly = pkgs.mkShell {
            nativeBuildInputs = nativeBuildInputs;
            buildInputs = buildInputs ++ (with pkgs; [
              rustToolchainNightly
            ]);
          };
        };

        packages = rec {
          default = scryer-prolog;
          scryer-prolog = pkgs.rustPlatform.buildRustPackage {
            pname = name;
            inherit version;
            src = ./.;
            nativeBuildInputs = nativeBuildInputs;
            buildInputs = buildInputs;
            cargoLock = {
              lockFile = ./Cargo.lock;
            };
            release = true;
          };
        };
      }
    );
}
