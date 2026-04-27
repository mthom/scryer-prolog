#!/usr/bin/env bash
set -e

echo "Checking all feature at once"
cargo check -q --all-targets --all-features "$@"

features=$(cargo metadata  --no-deps --format-version  1 | jq -r '.packages[] | select(.name = "scryer-prolog") | .features | keys | join(" ")')

for feature in ${features} ; do
	echo "Checking feature ${feature} in isolation"
	cargo check -q --all-targets --no-default-features --features=${feature} "$@"
done
