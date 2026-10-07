#!/usr/bin/env bash
# Usage: encoding-pilot-worker.sh <base>, from a worker's worktree.
# Checks that the worktree is clean and has the same Canonical source as <base>,
# then copies the build directory from the main checkout and builds `debug`.
set -euo pipefail

BASE=$1
MAIN=$(cd "$(dirname "$0")/../.." && pwd)
SOURCE=(Canonical.lean Canonical lakefile.lean ':!Canonical/Test')

if [ -n "$(git status --porcelain)" ] || ! git diff --quiet "$BASE" HEAD -- "${SOURCE[@]}"; then
  echo "This worktree is not clean at $BASE:"
  git log --oneline -1
  git status --short | head -20
  exit 1
fi

rsync -a --delete "$MAIN/.lake/" .lake/
lake build debug
