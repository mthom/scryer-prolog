#!/usr/bin/env bash
set -e

echo Cleanup workspace build artifacts and extra target output

# clean just the direct members of the current workspace, use cargo metadata to generalize to all rust projects
cargo clean --workspace

# remove directories in /target/ that are not named `debug` or `release`
before=`du -s target | awk '{print $1}'`
find ./target -maxdepth 1 -type d ! -name debug ! -name release ! -name target -exec rm -r {} \;
after=`du -s target | awk '{print $1}'`
echo Deleted $(($before - $after)) bytes from target directory
