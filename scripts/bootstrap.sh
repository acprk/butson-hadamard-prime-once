#!/usr/bin/env bash
# Prepare dependencies: check for elan/lake, then fetch the pinned Mathlib build cache.
set -euo pipefail

project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$project_root"

if ! command -v elan >/dev/null 2>&1 && ! command -v lake >/dev/null 2>&1; then
  printf '%s\n' 'elan not found. Install it first: https://github.com/leanprover/elan' >&2
  exit 1
fi
if ! command -v lake >/dev/null 2>&1; then
  printf '%s\n' 'lake not on PATH. Add ~/.elan/bin to PATH and rerun.' >&2
  exit 1
fi

# elan selects the toolchain pinned in lean-toolchain (leanprover/lean4:v4.34.1).
printf 'Toolchain: %s\n' "$(cat lean-toolchain)"
lake --version

# Clone Mathlib and its dependencies at the revisions recorded in lake-manifest.json,
# then download the matching prebuilt Mathlib .olean cache.
lake exe cache get

printf '%s\n' 'Dependencies and Mathlib cache prepared. Run lake build or bash scripts/check-proof.sh.'
