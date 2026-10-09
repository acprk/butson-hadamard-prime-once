#!/usr/bin/env bash
# Run the proof checks, then replay the audit target in Lean's kernel with leanchecker.
set -euo pipefail
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"

project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$project_root"
bash scripts/check-proof.sh

# leanchecker ships with the Lean toolchain (v4.34.1 includes it). It re-checks the audit
# module and every declaration it imports (Mathlib included) in a fresh environment.
# This is Lean's own kernel, not an independent kernel implementation. Expect roughly
# 45-60 minutes and about 7 GB of memory (it replays all of Mathlib in one process).
if ! lake env which leanchecker >/dev/null 2>&1; then
  printf '%s\n' 'leanchecker is not available in this toolchain; kernel replay skipped.' >&2
  exit 2
fi
lake env leanchecker --fresh OAI.LinearAlgebra.CirculantHadamard.PrimeOnceAudit
printf '%s\n' 'OK: leanchecker --fresh replay of OAI.LinearAlgebra.CirculantHadamard.PrimeOnceAudit passed.'
