#!/usr/bin/env bash
set -e

echo Cleanup workspace build artifacts and extra target output

# clean just the direct members of the current workspace, with cargo metadata should generalize to all rust projects
cargo clean -p `cargo metadata --format-version 1 | jq -r '[.workspace_members[]|split(" ")|.[0]]|join(" ")'`

# remove directories in /target/ that are not named `debug` or `release`
find ./target -maxdepth 1 -type d ! -name debug ! -name release ! -name target -exec rm -r {} \;
