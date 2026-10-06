#!/usr/bin/env bash
# Prepare for an encoding-pilot run: copy this checkout into the Mathlib harness and build the baseline.
# Prints the base commit, to pass to the workflow as `args.base`.
set -euo pipefail

REPO=$(git rev-parse --show-toplevel)
HARNESS=$HOME/Canonical/lean
PKG=$HARNESS/.lake/packages/Canonical

if [ -n "$(git -C "$REPO" status --porcelain --untracked-files=no)" ]; then
  echo "Commit first: worktrees are made from HEAD, so uncommitted changes would not be in the workers' base." >&2
  exit 1
fi
BASE=$(git -C "$REPO" rev-parse HEAD)

lake -d "$REPO" build debug

rsync -a --delete --exclude .claude "$REPO/" "$PKG/"
lake -d "$HARNESS" build Canonical
lake -d "$HARNESS" env lean "$HARNESS/Results/ITP.lean"

# Lake may check the package out to the revision in the harness manifest; the run is invalid if it did.
if [ "$(git -C "$PKG" rev-parse HEAD)" != "$BASE" ]; then
  echo "The harness package is no longer at $BASE after building." >&2
  exit 1
fi
echo "$BASE"
