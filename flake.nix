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
        buildInputs = with pkgs; [ openssl ];
      in
      {
        devShells = {
          default = pkgs.mkShell {
            nativeBuildInputs = nativeBuildInputs;
            buildInputs = buildInputs ++ (with pkgs; [
              rustToolchainDev
            ]);
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
