#!/usr/bin/env bash
# Usage: encoding-pilot-evaluate.sh <base> < diff
# Applies the diff to the Mathlib harness's Canonical package, builds Results/ITP.lean, and undoes the diff.
# Exit codes: 0 builds, 1 the harness package is not clean at <base>, 2 the diff does not apply,
# 3 the build fails, 75 the harness is busy (another evaluation held it for 8 minutes; run again).
set -uo pipefail

HARNESS=$HOME/Canonical/lean
PKG=$HARNESS/.lake/packages/Canonical

# Hold the harness for the rest of this script, waiting at most 8 minutes for it.
if [ -z "${HARNESS_LOCKED:-}" ]; then
  HARNESS_LOCKED=1 exec lockf -t 480 "$HARNESS/.lake/encoding-pilot.lock" "$0" "$@"
fi

BASE=$1
DIFF=$(mktemp)
cat > "$DIFF"

if [ "$(git -C "$PKG" rev-parse HEAD)" != "$BASE" ] || [ -n "$(git -C "$PKG" status --porcelain)" ]; then
  echo "The harness package is not clean at $BASE:"
  git -C "$PKG" log --oneline -1
  git -C "$PKG" status --short | head -20
  exit 1
fi

if ! git -C "$PKG" apply "$DIFF"; then
  echo "The diff does not apply."
  exit 2
fi

status=0
{ lake -d "$HARNESS" build Canonical && lake -d "$HARNESS" lean "$HARNESS/Results/ITP.lean"; } > "$DIFF.log" 2>&1 || status=3
git -C "$PKG" apply -R "$DIFF"

if [ $status -eq 0 ]; then
  echo "Builds."
else
  echo "The build fails:"
  grep -A3 '^error' "$DIFF.log" | head -40 || tail -20 "$DIFF.log"
fi
exit $status
