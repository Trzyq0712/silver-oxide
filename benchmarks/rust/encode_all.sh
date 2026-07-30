#!/usr/bin/env bash
# Encode every benchmark source in src/ to vpr/ via Prusti.
#
# Usage: encode_all.sh [name ...]      # no args = all of src/*.rs
#
# ~2-3 min and ~1 MB of Viper per source, which is why vpr/ is committed: measurement
# runs never need Prusti. Skips a source whose .vpr is newer than it. Encoding failures
# are reported and skipped, not fatal — an unsupported feature drops one benchmark, not
# the run.
set -uo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
mkdir -p "$here/vpr"

if [[ $# -gt 0 ]]; then
    sources=()
    for name in "$@"; do
        sources+=("$here/src/${name%.rs}.rs")
    done
else
    sources=("$here"/src/*.rs)
fi

failed=()
for src in "${sources[@]}"; do
    stem="$(basename "$src" .rs)"
    out="$here/vpr/$stem.vpr"
    if [[ -f "$out" && "$out" -nt "$src" ]]; then
        echo "[skip] $stem (vpr newer than src)"
        continue
    fi
    echo "[encode] $stem"
    if ! "$repo/tools/prusti_encode.sh" "$src" "$out"; then
        echo "[FAILED] $stem" >&2
        failed+=("$stem")
    fi
done

if [[ ${#failed[@]} -gt 0 ]]; then
    echo "encode failures: ${failed[*]}" >&2
    exit 1
fi
