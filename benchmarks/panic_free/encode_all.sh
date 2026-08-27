#!/usr/bin/env bash
# Encode every panic-freedom source in src/ to vpr/ via Prusti, WITH overflow checks.
#
# Usage: encode_all.sh [name ...]      # no args = all of src/*.rs
#
# The difference from ../rust/encode_all.sh is PRUSTI_CHECK_OVERFLOWS=true: the perf
# corpus turns overflow checks off (they add obligations, not block structure), while
# this corpus exists precisely to exercise them. Everything else — skip-if-newer,
# non-fatal per-source failure — matches.
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
    if ! PRUSTI_CHECK_OVERFLOWS=true "$repo/tools/prusti_encode.sh" "$src" "$out"; then
        echo "[FAILED] $stem" >&2
        failed+=("$stem")
    fi
done

if [[ ${#failed[@]} -gt 0 ]]; then
    echo "encode failures: ${failed[*]}" >&2
    exit 1
fi
