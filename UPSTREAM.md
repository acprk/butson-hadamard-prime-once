# Upstream provenance

This repository is a standalone Lake project. It contains new Lean modules together with a
small, unmodified extract of the Lean library of
[OpenAI's mathematics repository](https://github.com/openai/math), taken at commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` ("Merge pull request #1 from
openai/codex/update-10-7", 2026-10-07):

https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/LinearAlgebra/CirculantHadamard

The upstream files belong to OpenAI's formalization accompanying the preprint *The circulant
Hadamard conjecture* (OpenAI, September 23, 2026), available at the same revision under
`preprints/The-circulant-Hadamard-conjecture-September-23-2026`.

## Files copied unmodified (28)

These files are the import closure, within `OAI.*`, of the new `RamifiedComparison` modules.
The new `TheoremS` modules import only Mathlib. Each file is byte-identical to
`git show fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb:lean/<path>`. Paths are relative to `lean/`:

```
OAI/LinearAlgebra/CirculantHadamard/AlternatingLocalization.lean
OAI/LinearAlgebra/CirculantHadamard/AlternatingProducts.lean
OAI/LinearAlgebra/CirculantHadamard/CoefficientEvaluation.lean
OAI/LinearAlgebra/CirculantHadamard/CyclicEvaluation.lean
OAI/LinearAlgebra/CirculantHadamard/CyclicEvaluationAt.lean
OAI/LinearAlgebra/CirculantHadamard/CyclicEvaluationProjection.lean
OAI/LinearAlgebra/CirculantHadamard/CyclicPolynomial.lean
OAI/LinearAlgebra/CirculantHadamard/CyclicProjection.lean
OAI/LinearAlgebra/CirculantHadamard/CyclicProjectionPolynomial.lean
OAI/LinearAlgebra/CirculantHadamard/CyclicRing.lean
OAI/LinearAlgebra/CirculantHadamard/CyclicScalarDivision.lean
OAI/LinearAlgebra/CirculantHadamard/CyclotomicAwayLocal.lean
OAI/LinearAlgebra/CirculantHadamard/CyclotomicFactorDivision.lean
OAI/LinearAlgebra/CirculantHadamard/CyclotomicLocalBase.lean
OAI/LinearAlgebra/CirculantHadamard/CyclotomicProjection.lean
OAI/LinearAlgebra/CirculantHadamard/CyclotomicRemainder.lean
OAI/LinearAlgebra/CirculantHadamard/CyclotomicRings.lean
OAI/LinearAlgebra/CirculantHadamard/LocalComparison.lean
OAI/LinearAlgebra/CirculantHadamard/LocalComparisonInduction.lean
OAI/LinearAlgebra/CirculantHadamard/LocalDVR.lean
OAI/LinearAlgebra/CirculantHadamard/LocalizationIntersection.lean
OAI/LinearAlgebra/CirculantHadamard/LocalizationMaps.lean
OAI/LinearAlgebra/CirculantHadamard/PrimeCharacterEvaluations.lean
OAI/LinearAlgebra/CirculantHadamard/PrimeComponents.lean
OAI/LinearAlgebra/CirculantHadamard/RamifiedEisenstein.lean
OAI/LinearAlgebra/CirculantHadamard/RamifiedLocal.lean
OAI/LinearAlgebra/CirculantHadamard/RamifiedUnit.lean
OAI/LinearAlgebra/CirculantHadamard/ResidueOneAssociation.lean
```

To check that they are unmodified, from a clone of openai/math:

```sh
for f in $(sed -n '/^OAI\//p' UPSTREAM.md); do
  git -C /path/to/openai-math show fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb:lean/$f | cmp - lean/$f
done
```

The module paths (`OAI/LinearAlgebra/CirculantHadamard/...`) are kept, so the namespaces of
the upstream files are unchanged. No other upstream file is included. The rest of OpenAI's
circulant Hadamard formalization (its `Main` theorem and the other modules) and all other
projects of the upstream library are omitted, along with their dependencies
(fixed-point-theorems and the other packages in the upstream `lakefile.lean`). They remain
available at the pinned upstream revision.

## Toolchain and dependencies

The upstream Lean toolchain (`leanprover/lean4:v4.34.1`) and Mathlib revision
(`d13f23b723b8a846827a245b89c10fc7d3f11612`) are kept. `lake-manifest.json` keeps Mathlib and
its transitive dependencies at exactly the upstream revisions.

## New files (not from upstream)

- `lean/OAI/LinearAlgebra/CirculantHadamard/TheoremS/` — `Core`, `Cyclotomic`,
  `Decomposition`, `LocalRing`, `Product`, `Main`, `Sharp`, `RDS` (Theorem S, S′, Corollary R).
- `lean/OAI/LinearAlgebra/CirculantHadamard/RamifiedComparison/` — `Core`, `Localized`,
  `PrimeCyclotomic`, `LemmaA`, `Auxiliary`, `TheoremC`, `PrimePower` (Lemma A, Theorem C).
- `lean/OAI/LinearAlgebra/CirculantHadamard/PrimeOnceAudit.lean` — guarded axiom audit.
- `lean/OAI.lean`, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, `scripts/`,
  `paper/`, `computations/`, `verification/` and the top-level documents.

The new Lean modules were developed in a working copy of openai/math. They were committed
there on top of `fd4aeeb2e` (the `RamifiedComparison` modules in local commits up to
`08fcd618213a`, which were never pushed). This repository records the extracted sources only;
it does not retain that history.

## License and attribution

The upstream [Apache License 2.0](LICENSE) is retained and applies to the whole repository.
The upstream files have no individual headers and are unmodified, so no modification notices
are added. The original authorship of these files remains with OpenAI. No historical-priority
claim and no claim about the original authors' intentions is made.
