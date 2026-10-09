#!/usr/bin/env bash
# Build the formalization and its axiom audit; fail on any sorry/admit or extra axiom.
set -euo pipefail

# Whole-Mathlib imports make each worker memory-heavy. Allow explicit overrides.
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"

project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$project_root"

# 1. Source scan: no `sorry`, `admit` or user-declared axioms anywhere under lean/.
if grep -rnwE --include='*.lean' 'sorry|admit|sorryAx' lean/; then
  printf '%s\n' 'FAIL: sorry/admit found in lean/ (see above).' >&2
  exit 1
fi
if grep -rnE --include='*.lean' '^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+)?axiom[[:space:]]' lean/; then
  printf '%s\n' 'FAIL: axiom declaration found in lean/ (see above).' >&2
  exit 1
fi

# 2. Build everything (default target OAI, which imports the audit).
log="$(mktemp)"
trap 'rm -f -- "$log"' EXIT
lake build 2>&1 | tee "$log"
if grep -q "declaration uses 'sorry'\|declaration uses \`sorry\`" "$log"; then
  printf '%s\n' 'FAIL: Lean reported a declaration using sorry.' >&2
  exit 1
fi

# 3. The audit module pins the exact `#print axioms` output of every public theorem to
#    [propext, Classical.choice, Quot.sound]; any other axiom makes this build fail.
lake build OAI.LinearAlgebra.CirculantHadamard.PrimeOnceAudit

printf '%s\n' 'OK: build passed, no sorry, axioms limited to propext / Classical.choice / Quot.sound.'
