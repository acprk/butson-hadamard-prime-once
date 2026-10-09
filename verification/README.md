# Verification records

## `mock-reviews/`

These are five simulated referee reports written by **AI agents** (Claude) that did not write
the paper. They are **not human peer review**. They are kept verbatim as a record, and most are
written in Chinese. File names mention `preprintBH/`, the working directory of the draft, and
`/tmp/...` paths of the reviewers' throw-away scripts.

| File | Object reviewed |
| --- | --- |
| `R1-JCTA.txt` | earlier 24-page draft, reviewed as for J. Combin. Theory Ser. A |
| `R2-SIDMA.txt` | the same 24-page draft, reviewed as for SIAM J. Discrete Math. |
| `R3-shortS.txt` | 12-page revision (Theorem S′ only) |
| `R4-noteC.txt` | separate note on the ramified regime (Lemma A, Theorems B, C), later merged |
| `R5-final.txt` | the merged 18-page version in `../paper/` (final mock review) |
| `MERGED-FIXES.md` | merged fix list after R1/R2, used for the revision |

## `scripts/`

These are brute-force sanity checks, independent of the proofs. They enumerate all
`a : ℤ/n → μ_h` with `a(0) = 1` and test perfect autocorrelation in floating point.

- `s_check.py`: Theorem S predicts 0 for `(6,4)`, `(10,4)`, `(6,8)`, `(3,2)`, `(6,5)`, `(5,4)`,
  `(12,4)`; positive controls `(4,4)`, `(4,2)`, `(9,3)`, `(5,5)`, `(2,4)`, `(8,4)`.
- `s2_check.py`: condition (ii) (`n ≡ h ≡ 2 mod 4`) predicts 0; controls with `4 ∣ h`.

```sh
python3 verification/scripts/s_check.py
python3 verification/scripts/s2_check.py
```

Both are pure Python with exponential running time; together they take about 12 s on one core.
