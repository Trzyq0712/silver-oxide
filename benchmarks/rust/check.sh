#!/usr/bin/env bash
# Verify every .vpr in vpr/ and hold the corpus to its rule: every member verifies,
# except the members listed in expected_failures.txt.
#
# Usage: check.sh [stem ...]        # no args = every vpr/*.vpr
#
# Exit 1 on any difference from expected_failures.txt, in either direction:
#   REGRESSED — a member fails that is not on the list (what this guards against);
#   STALE     — a listed member verifies, so the entry must be deleted.
# Unlike ../panic_free/check.sh there is no sound/incomplete distinction here: these
# sources carry no assertions of their own, so a FAIL is always our incompleteness.
set -uo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
verify="$repo/target/release/verify"
expected="$here/expected_failures.txt"

[[ -x "$verify" ]] || { echo "build first: cargo build --release --bin verify" >&2; exit 2; }

if [[ $# -gt 0 ]]; then
    stems=("$@")
else
    mapfile -t stems < <(cd "$here/vpr" && ls -1 *.vpr 2>/dev/null | sed 's/\.vpr$//')
fi
[[ ${#stems[@]} -gt 0 ]] || { echo "no .vpr in vpr/ (run ./encode_all.sh)" >&2; exit 2; }

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# "<stem> <member>" lines, comments and blanks dropped.
grep -v '^\s*#' "$expected" | awk 'NF {print $1, $2}' | sort > "$work/expected"

regressed=0
stale=0
ok=0
allowed=0

for stem in "${stems[@]}"; do
    vpr="$here/vpr/$stem.vpr"
    [[ -f "$vpr" ]] || { echo "[no-vpr] $stem (run ./encode_all.sh)" >&2; exit 2; }

    if ! "$verify" "$vpr" > "$work/$stem.out" 2>"$work/$stem.err"; then
        # A non-zero exit with no [FAIL] line is a pipeline error, not a failed member.
        if ! grep -q '\[FAIL\]' "$work/$stem.out"; then
            echo "PIPELINE  $stem ($(tail -1 "$work/$stem.err"))"
            regressed=$((regressed + 1))
            continue
        fi
    fi

    while read -r member; do
        if grep -qx "$stem $member" "$work/expected"; then
            echo "STALE     $stem::$member (now verifies — delete it from expected_failures.txt)"
            stale=$((stale + 1))
        else
            ok=$((ok + 1))
        fi
    done < <(sed -n 's/.*\[OK\] \([^:]*\).*/\1/p' "$work/$stem.out")

    while read -r member reason; do
        if grep -qx "$stem $member" "$work/expected"; then
            allowed=$((allowed + 1))
        else
            echo "REGRESSED $stem::$member ($reason)"
            regressed=$((regressed + 1))
        fi
    done < <(sed -n 's/.*\[FAIL\] \([^:]*\): *\(.*\)/\1 \2/p' "$work/$stem.out")
done

echo
echo "verified: $ok   known-failing: $allowed   regressed: $regressed   stale: $stale"
[[ $regressed -eq 0 && $stale -eq 0 ]] || exit 1
