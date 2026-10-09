# Group-invariant Butson Hadamard matrices: a prime dividing the order exactly once

This repository contains a short paper and its Lean 4 formalization. The main theorem says that
if a prime `p` divides the order of a finite abelian group `G` exactly once and `p` is
unramified in `ℚ(ζ_h)`, then there is no `G`-invariant Butson Hadamard matrix `BH(G,h)`.
Equivalently, there is no generalized bent function `G → ℤ_h`, and, for cyclic `G`, no perfect
sequence of length `|G|` over the `h`-th roots of unity `μ_h`. A second part treats the
ramified family `BH(pq^e, p)`, where the main theorem does not apply.

The results were found, verified and formalized by **Claude (Anthropic) agents** working under
the direction of the repository owner, [AUTHOR NAME]. Lean checked the formal proofs; the
verification scope is documented below. **No human peer review has taken place.** See
[Status and caveats](#status-and-caveats) before you rely on any statement here.

**Paper:** [*Group-Invariant Butson Hadamard Matrices and a Prime Dividing the Order Exactly
Once*](paper/main.pdf) ([LaTeX source](paper/main.tex), [build instructions](paper/README.md)).

The Lean development sits on top of a small part of the Lean library of
[OpenAI's mathematics repository](https://github.com/openai/math), commit
[`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/LinearAlgebra/CirculantHadamard).
The Theorem S modules depend only on Mathlib. The ramified-comparison modules import 28
unmodified upstream files from OpenAI's circulant Hadamard formalization; see
[UPSTREAM.md](UPSTREAM.md) for provenance.

## What is proved

All statements below are in Lean (namespace `OAI.CirculantHadamard.TheoremS`, or
`OAI.CirculantHadamard.RamifiedComparison` for Lemma A and Theorem C). Perfect autocorrelation
`∑_g a(g + s) * conj (a g) = 0` for all `s ≠ 0` is the coefficient form of `X X^* = |G|` in
`ℂ[G]`, where `X = ∑ a(g) g`. A `μ_h`-valued function with this property is the same thing as a
`G`-invariant `BH(G,h)`.

### Theorem S′ (sharp form)

Let `G` be a finite abelian group and `p` a prime with `p ∥ |G|`. If `p` is unramified in
`ℚ(ζ_h)`, that is, `p ∤ h`, or `p = 2` and `4 ∤ h`, then there is no `BH(G,h)`.
From [`TheoremS/Sharp.lean`](lean/OAI/LinearAlgebra/CirculantHadamard/TheoremS/Sharp.lean):

```lean
theorem no_perfect_function_sharp (G : Type*) [AddCommGroup G] [Fintype G] (h p : ℕ)
    (hp : p.Prime) (hpG : p ∣ Fintype.card G) (hp2 : ¬ p ^ 2 ∣ Fintype.card G)
    (hunr : ¬ p ∣ h ∨ (p = 2 ∧ ¬ 4 ∣ h)) (a : G → ℂ) (ha : ∀ g, a g ^ h = 1)
    (hperf : ∀ s ≠ 0, ∑ g, a (g + s) * conj (a g) = 0) : False
```

The cyclic case is `no_perfect_sequence_sharp` (with `G = ZMod n`). The unsharpened form
`p ∤ h` is `no_perfect_function` / `no_perfect_sequence` in
[`TheoremS/Main.lean`](lean/OAI/LinearAlgebra/CirculantHadamard/TheoremS/Main.lean). Its
quaternary special case reads:

```lean
theorem no_perfect_quaternary_sequence (N p : ℕ) [NeZero N] (hp : p.Prime) (hodd : p ≠ 2)
    (hpN : p ∣ N) (hp2 : ¬ p ^ 2 ∣ N) (a : ZMod N → ℂ) (ha : ∀ x, a x ^ 4 = 1)
    (hperf : ∀ s ≠ 0, ∑ x, a (x + s) * conj (a x) = 0) : False
```

### Do Duc's condition (ii) and the square-free corollary

Do Duc conjectured that a `BH(ℤ_n, h)` exists if and only if (i) `ν_p(h) ≥ ⌈ν_p(n)/2⌉` for
every prime `p ∣ n`, and (ii) `ν_2(h) ≥ 2` if `n ≡ 2 (mod 4)`. Theorem S′ proves that condition
(i) is necessary at every prime with `ν_p(n) = 1`, and that condition (ii) is necessary, for
every abelian group of order `n`. For `G = ℤ/n` and `h ≡ 2 (mod 4)`, condition (ii) is the
following Lean theorem:

```lean
theorem no_perfect_sequence_two_mod_four (n h : ℕ) [NeZero n] (hn : n % 4 = 2) (hh : h % 4 = 2)
    (a : ZMod n → ℂ) (ha : ∀ x, a x ^ h = 1)
    (hperf : ∀ s ≠ 0, ∑ x, a (x + s) * conj (a x) = 0) : False
```

(For odd `h` it is the case `p = 2` of `no_perfect_function`.) Together with the known
constructions of Mow and Duc–Schmidt, this gives the **square-free corollary**: *if `n` is
square-free, a `BH(ℤ_n, h)` exists if and only if `n ∣ h` and, for even `n`, `4 ∣ h`.* So the
conjectures of Mow and of Do Duc hold for square-free lengths. The constructions used for the
"if" direction are cited, not formalized.

### Corollary R (relative difference sets)

Let `G` be a finite abelian group, `N ≤ G` with `|N| = n`, `|G/N| = m`, and let `D` be a
semi-regular `(m, n, m, m/n)`-RDS in `G` relative to `N`. If `p ∥ m`, then `N` is a `p`-group.
No splitting hypothesis is needed. In Lean, `D` is the image of a section `σ` of `π : G →+ Q`.
"`N` is not a `p`-group" is witnessed by a nonzero `x ∈ ker π` of order prime to `p`. From
[`TheoremS/RDS.lean`](lean/OAI/LinearAlgebra/CirculantHadamard/TheoremS/RDS.lean), with
`{G Q : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] [AddCommGroup Q] [Fintype Q]
[DecidableEq Q]`:

```lean
theorem no_semiregular_rds (π : G →+ Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q) (lam : ℕ)
    (hrds : ∀ g, π g ≠ 0 → (univ.filter (fun z : Q × Q => σ z.1 - σ z.2 = g)).card = lam)
    (p : ℕ) (hp : p.Prime) (hpQ : p ∣ Fintype.card Q) (hp2 : ¬ p ^ 2 ∣ Fintype.card Q)
    (x : G) (hx0 : x ≠ 0) (hxN : π x = 0) (hxp : ¬ p ∣ addOrderOf x) : False
```

### Lemma A and Theorem C (the ramified regime)

For `BH(pq^e, p)` with `p` odd and `e ≥ 2`, the only prime dividing the length exactly once is
`p`, and `p` ramifies in `ℚ(ζ_p)`, so Theorem S′ does not apply. **Lemma A** is a comparison
lemma at the ramified prime. Let `O = 𝓞 K` with `K = ℚ(ζ_{pd})`, `p ∤ d`. If `F V = n` in
`O[C_p]` with `n ∈ ℤ`, `v_p(n) = 1`, then for each prime `P` of `O` above `p` the values
`F(ζ_p^j)` all have the same `P`-valuation `α`, and they are all congruent to `F(1)` modulo
`P^(α+1)`. From
[`RamifiedComparison/LemmaA.lean`](lean/OAI/LinearAlgebra/CirculantHadamard/RamifiedComparison/LemmaA.lean),
with `{K : Type*} [Field K] [NumberField K]`:

```lean
theorem lemmaA (p d : ℕ) [hp : Fact p.Prime] (hd : ¬ p ∣ d)
    [IsCyclotomicExtension {p * d} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (P : Ideal (𝓞 K)) [hP : P.IsPrime] [hPo : P.LiesOver (Ideal.span {(p : ℤ)})]
    (u v : ZMod p → 𝓞 K) (n : ℤ) (hn₁ : (p : ℤ) ∣ n) (hn₂ : ¬ (p : ℤ) ^ 2 ∣ n)
    (huv : ∀ τ : ZMod p, ∑ a, u a * v (τ - a) = if τ = 0 then (n : 𝓞 K) else 0) :
    ∃ α : ℕ, ∀ j : ℕ,
      ∑ a, u a * hζ.toInteger ^ (j * a.val) ∈ P ^ α ∧
      ∑ a, u a * hζ.toInteger ^ (j * a.val) ∉ P ^ (α + 1) ∧
      (∑ a, u a * hζ.toInteger ^ (j * a.val)) - ∑ a, u a ∈ P ^ (α + 1)
```

**Theorem C(i).** For primes `p ≠ q` and every `e ≥ 1` there is no perfect sequence of length
`pq^e` over `μ_p`. From
[`RamifiedComparison/PrimePower.lean`](lean/OAI/LinearAlgebra/CirculantHadamard/RamifiedComparison/PrimePower.lean):

```lean
theorem not_exists_perfect_prime_power_phase (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (e : ℕ) (he : 1 ≤ e) :
    ¬ ∃ a : ZMod (p * q ^ e) → ℂ,
      (∀ j, a j ^ p = 1) ∧
      ∀ τ : ZMod (p * q ^ e), τ ≠ 0 →
        ∑ j, a j * (starRingEnd ℂ) (a (j + τ)) = 0
```

The case `e = 1` is also stated separately as `not_exists_perfect_prime_phase` in
[`TheoremC.lean`](lean/OAI/LinearAlgebra/CirculantHadamard/RamifiedComparison/TheoremC.lean).
The paper's Theorem C(ii) (an extra self-conjugate cofactor `u`) is not formalized.

## Proof idea

Since `p ∥ |G|`, the Sylow `p`-subgroup is cyclic of order `p` and a direct factor:
`G = H × C_p` with `p ∤ |H|`. Write `X = ∑_k c_k T^k` with columns `c_k ∈ ℤ[ζ_h][H]` whose
`|H|` coefficients are roots of unity. If `h ≡ 2 (mod 4)` and `p = 2`, replace `h` by
`h' = h/2`. Then `h'` is odd and `μ_h = ±μ_{h/2}`, so every coefficient still lies in
`ℤ[ζ_{h'}]` and `p ∤ h'`. Take `O = ℤ[ζ_L]` with `L = lcm(h', exp H)`. Then `p` is unramified
in `O`; fix a prime `𝔭` above it. For each character `χ` of `H`, the partial evaluation
`X_χ = ∑_k χ(c_k) T^k ∈ O[C_p]` satisfies `X_χ X_χ^* = |G|`.

*Column lemma: one prime above `p`.* The residue field `F = O/𝔭` has characteristic `p`, so
`(O/𝔭)[C_p] ≅ F[T]/(T−1)^p`. This is a **local ring**: an element is a unit if and only if its
augmentation is nonzero. Since `v_𝔭(|G|) = 1` (because `p` is unramified), exactly one of
`X_χ(1)`, `conj X_χ(1)` lies in `𝔭`. The corresponding factor of `X_χ X_χ^* ≡ 0` is a unit, so
the other factor vanishes modulo `𝔭`. Hence all coefficients of `X_χ` lie in a single prime
`𝔮 ∈ {𝔭, conj 𝔭}`, and in particular `χ(c_k) conj χ(c_k) ∈ 𝔭` for all `χ` and `k`.

*Parseval on a single coset.* Fix **one** `k`. Parseval on `H` gives
`∑_χ |χ(c_k)|² = |H| ∑_x |c_k(x)|² = |H|²`, because each `c_k(x)` is a root of unity. The left
side lies in `𝔭`, so `|H|² ∈ 𝔭 ∩ ℤ = pℤ`. This contradicts `p ∤ |H|`. Summing over all `k`
(that is, Parseval on all of `G`) would only give `p|H|² ∈ 𝔭`, which is no contradiction.
The single-coset restriction is the essential step.

If `p` ramifies in `ℚ(ζ_h)`, then `v_𝔭(|G|) ≥ 2` and the first step fails. Lemma A replaces it
at the ramified prime. It expands in the uniformizer `ζ_p − 1`; the digits of `F(ζ_p^j)` are
polynomials in `j` of degree less than `p − 1`, and comparing them over the `p` points of
`F_p` forces equal valuations and the congruence. Theorem C combines Lemma A at `p` with a
comparison at the primes above `q`.

## Consequences

The numbers below are taken from the paper. "Not excluded by any result known to us" refers
only to the earlier criteria the authors identified and implemented. The list of earlier
criteria is not claimed to be complete.

- **Do Duc's list.** Of the 2687 pairs `(n,h)`, `n,h ≤ 100`, listed as open in Do Duc
  (2019, Remark 3.13), Theorem S′ excludes **2323**: 2262 with a prime `p`, `ν_p(n) = 1`,
  `p ∤ h`, and 61 more with `n ≡ h ≡ 2 (mod 4)`. Of these, 237 + 23 are covered by earlier
  criteria we could identify. The remaining **2063 = 2025 + 38** pairs are not excluded by any
  result known to us, **subject to Leung–Chue–Zhao (DCC 93, 2025)**, whose full text we have
  not read. 474 of the 2063 have `n = 2p` with `p` an odd prime, 17 of them with `n = 6`; this
  is the subset most likely to overlap with that paper.
- **Arasu's list.** The eleven orders 260, 340, 442, 468, 520, 580, 680, 754, 820, 884, 890 are
  all orders `≤ 1000` for which, according to Arasu's survey (2011), a circulant complex Hadamard
  matrix had not been excluded. All eleven are excluded (`h = 4`, using an odd prime of
  exponent 1). In Lean only the general `no_perfect_quaternary_sequence` is verified; the
  eleven instances are not. The statement "only `N ∈ {1, 2, 4, 8, 16}` remain for `N ≤ 1000`"
  relies on Arasu's remark.
- **Kumar–Scholtz–Welch, `m = 1`.** For `q ≡ 2 (mod 4)` there is no generalized bent function
  `ℤ_q → ℤ_q`.
- **Relative difference sets.** Corollary R contains every nonexistence statement of
  Leung–Schmidt–Zhang (2023, Sect. 6) and decides eight entries marked "?" in its tables.
- **The ramified regime.** Of the 334 lengths `pq^e ≤ 2000` with `p` odd and `e ≥ 2`, the
  earlier criteria we implemented exclude 300. Theorem C excludes the remaining **34 new
  lengths**: 56, 99, 112, 117, 184, 224, 248, 275, 297, 351, 448, 475, 496, 584, 621, 736,
  775, 847, 891, 896, 931, 992, 1053, 1269, 1375, 1421, 1472, 1504, 1593, 1775, 1792, 1813,
  1863, 1984. These include 56 and 99 from Yayla's table.

## Verification scope

| Statement | Status |
| --- | --- |
| Theorem S′ (`no_perfect_function_sharp`, `no_perfect_sequence_sharp`) | Lean |
| Theorem S for `p ∤ h` (`no_perfect_function`, `no_perfect_sequence`), quaternary case | Lean |
| Do Duc condition (ii) for `ℤ/n`, `h ≡ 2 (mod 4)` (`no_perfect_sequence_two_mod_four`) | Lean |
| Corollary R (`RDSCheck.no_semiregular_rds`) | Lean |
| Lemma A for `n ∈ ℤ`, `v_p(n) = 1` (`lemmaA`) | Lean |
| Theorem C(i), all primes `p ≠ q`, `e ≥ 1` (`not_exists_perfect_prime_power_phase`) | Lean |
| Square-free corollary, KSW `m = 1`, Arasu's eleven orders | derived on paper from the Lean statements |
| Lemma A for general `n ∈ O` with `v_𝔓(n) = p − 1`, Theorem B in general, Theorem C(ii) | paper only |
| Do Duc list counts, ramified-length counts, Appendix A, Lemma 3.6 | computation only (`computations/`) |

For every theorem in the first part of the table, `#print axioms` reports exactly
`[propext, Classical.choice, Quot.sound]`.
[`PrimeOnceAudit.lean`](lean/OAI/LinearAlgebra/CirculantHadamard/PrimeOnceAudit.lean) checks
this with `#guard_msgs`. It also checks `no_perfect_sequence` and
`not_exists_perfect_prime_phase`, ten theorems in total. Any other axiom, including `sorryAx`,
makes the build fail; a negative control with a user `axiom` and a `sorry` was confirmed to
fail. The sources contain no `sorry`, `admit` or `axiom` declaration.

The guards fix the axiom dependencies of the theorems. They do not show that the Lean
statements say what the paper says. Compare the statements quoted above with the paper
yourself; the definitions involved are Mathlib's (`ZMod`, `Fintype.card`, `𝓞 K`,
`IsCyclotomicExtension`, `Ideal.LiesOver`) together with explicit sums. The formal proof of
Theorem C uses `actual_local_character_association` from the copied OpenAI files at the primes
above `q`. Those upstream files are part of the checked import closure.

No proof depends on a computation. The computations in `computations/` support only the counts
in the Consequences section. They are stdlib-only Python scripts.

## Reproduction

Install [elan](https://github.com/leanprover/elan), Git and Python 3. From the repository root:

```sh
bash scripts/bootstrap.sh     # elan check + lake exe cache get (pinned Mathlib cache)
lake build                    # builds OAI: all public theorems and the axiom audit
bash scripts/check-proof.sh   # sorry/axiom source scan + build + guarded axiom audit
bash scripts/check-kernel.sh  # the above, then leanchecker --fresh replay of the audit
```

| Component | Pinned version |
| --- | --- |
| Lean | `leanprover/lean4:v4.34.1` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |

Mathlib is the only direct dependency; transitive revisions are in
[`lake-manifest.json`](lake-manifest.json). The Lake project is at the repository root
([`lakefile.lean`](lakefile.lean)), with sources under `lean/` (`srcDir := "lean"`). The entry
point [`lean/OAI.lean`](lean/OAI.lean) imports the public modules and the audit. Whole-Mathlib
imports make each worker memory-heavy; set `LEAN_NUM_THREADS` to suit your machine.

> **Local verification run, 2026-10-09** (Linux x86-64, Lean v4.34.1, Mathlib `d13f23b`, with a
> prebuilt Mathlib cache): `lake build` completed successfully (8969 jobs, 0 errors, no `sorry`;
> the only warning is an unused-section-variable lint in `TheoremS/RDS.lean`).
> `scripts/check-proof.sh` passed, and all ten `#print axioms` guards report exactly
> `[propext, Classical.choice, Quot.sound]`. A negative control with an added `axiom` and a
> `sorry` made the guards fail as intended. `lake env leanchecker --fresh
> OAI.LinearAlgebra.CirculantHadamard.PrimeOnceAudit` replayed the audit target and its whole
> import closure (Mathlib included) in Lean's kernel and exited 0 after about 47 minutes on one
> core. This is Lean's own kernel, not an independent checker. All computation scripts
> reproduced their committed output files byte for byte.

Paper and computations:

```sh
bash paper/build.sh                                   # pdflatex + bibtex -> paper/main.pdf
python3 computations/count2262/deduct.py              # Do Duc list: 2687 / 2262 + 61 / 2063
(cd computations/count2262 && python3 recon.py)       # independent reconstruction of the list
python3 computations/ramified/ramified_new.py         # 334 lengths pq^e <= 2000, 34 new
python3 computations/ramified/check_63_3.py           # (63,3) against Do Duc's criteria
python3 verification/scripts/s_check.py               # brute force: Theorem S small cases
python3 verification/scripts/s2_check.py              # brute force: condition (ii) small cases
```

`deduct.py`, `ramified_new.py` and `check_63_3.py` resolve paths relative to their own
location. `recon.py` must be run from `computations/count2262/`. The scripts rewrite their
output files in place (`remaining_*.txt`, `covered_with_reason.txt`, `ramified_new_2000.txt`);
`git diff` should then show no changes. The transcription `DoDuc_BH_open_cases.txt` has
SHA-256 `e225ca59474e7b0e21c393cfe850916e89cbf57ca08bd1be00ec7c1f70368f67`.

## Provenance

The 28 files listed in [UPSTREAM.md](UPSTREAM.md) are copied **unmodified** from
[openai/math](https://github.com/openai/math) at commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, path `lean/OAI/LinearAlgebra/CirculantHadamard/`.
They form the import closure of the `RamifiedComparison` modules within `OAI.*` and come from
OpenAI's formalization accompanying *The circulant Hadamard conjecture* (OpenAI, September 2026).
They are distributed under the [Apache License 2.0](LICENSE) of that repository, which is
retained here. The module paths are kept, so the namespaces and the upstream files are
byte-identical to the originals. The new modules are `TheoremS/`, `RamifiedComparison/` and
`PrimeOnceAudit.lean`, and they are distributed under the same license. No result of the (not
peer-reviewed) OpenAI preprint is used in the paper's proofs.

## Status and caveats

- **No human peer review.** The paper has not been submitted or refereed. The only reviews are
  five **mock reviews by AI agents** (in [`verification/mock-reviews/`](verification/mock-reviews/)),
  together with the list of fixes applied in response (`MERGED-FIXES.md`). They are not
  evidence of correctness in the sense of peer review.
- **Prior-art check pending.** We have not been able to read the full texts of the following
  paywalled references; the paper's statements about them are taken from abstracts or
  secondary sources and are marked as such:
  - K. H. Leung, J. H. E. Chue, M. Zhao, *On vanishing sums and cyclic Butson matrices*,
    Des. Codes Cryptogr. 93 (2025) 5143–5157 (**priority**: may overlap with the square-free
    corollary for `n = 6` and `n = 2p`, and with 474 of the 2063 pairs);
  - K. T. Arasu, W. de Launey, S. L. Ma, *On circulant complex Hadamard matrices*, Des. Codes
    Cryptogr. 25 (2002) 123–142;
  - S. L. Ma, *Planar functions, relative difference sets, and character theory*, J. Algebra
    185 (1996) 342–356;
  - S. L. Ma, W. S. Ng, *On non-existence of perfect and nearly perfect sequences*, Int. J.
    Inf. Coding Theory 1 (2009) 15–38;
  - A. Pott, *Finite Geometry and Character Theory*, LNM 1601 (1995), ch. 4;
  - D. Pei, *On non-existence of generalized bent functions* (1993);
  - M. Ikeda, *A remark on the non-existence of generalized bent functions* (1999);
  - K. Feng, F. Liu, *Non-existence of some generalized bent functions*, Acta Math. Sin. 19
    (2003) 39–50.

  Any of these may already contain Theorem S′ or some of its consequences.
- **No historical-priority claim** is made. "New" in this repository means "not found in the
  literature we were able to read".
- The Lean statements cover the scope in the table above. Corollaries marked "derived" and all
  counts depend on paper arguments, cited constructions and Python scripts.
- `paper/main.tex` is the draft as reviewed. Its author block is empty. Its AI-use statement is
  a draft, and its artifact paragraph (Sect. 5.3) still describes the pre-release Lean branch
  rather than this repository.

## AI attribution

The results in this repository (the theorems, their proofs, the Lean formalization, the
computations and the paper text) were found, verified and formalized by Claude (Anthropic)
agents working under the direction of the repository owner, [AUTHOR NAME]. Lean checked the
formal proofs. The mock reviews were also produced by AI agents. The human owner directed the
work and is responsible for its release.

## Citation

See [`CITATION.cff`](CITATION.cff). Cite OpenAI's circulant Hadamard formalization separately
when you use the upstream files.
