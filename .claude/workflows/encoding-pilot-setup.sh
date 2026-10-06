#!/usr/bin/env bash
# Prepare for an encoding-pilot run: check that the Mathlib harness uses the same Canonical source the workers
# start from (HEAD of this checkout), and build the baseline. Prints the base commit, for `args.base`.
set -euo pipefail

REPO=$(git rev-parse --show-toplevel)
HARNESS=$HOME/Canonical/lean
PKG=$HARNESS/.lake/packages/Canonical
SOURCE=(Canonical.lean Canonical lakefile.lean ':!Canonical/Test')

# Workers' worktrees are made from HEAD, so the source the harness builds must match HEAD's.
if [ -n "$(git -C "$REPO" status --porcelain --untracked-files=no -- "${SOURCE[@]}")" ]; then
  echo "Commit first: uncommitted changes to Canonical's source would not be in the workers' base." >&2
  exit 1
fi
lake -d "$HARNESS" build Canonical
BASE=$(git -C "$PKG" rev-parse HEAD)
if ! git -C "$REPO" diff --quiet "$BASE" HEAD -- "${SOURCE[@]}"; then
  echo "The harness's Canonical ($BASE) differs from HEAD; release HEAD and update the harness." >&2
  exit 1
fi

lake -d "$REPO" build debug
lake -d "$HARNESS" lean "$HARNESS/Results/ITP.lean"
echo "$BASE"
