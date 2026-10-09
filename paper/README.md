# Group-Invariant Butson Hadamard Matrices and a Prime Dividing the Order Exactly Once

[Read the paper (PDF)](main.pdf) · [LaTeX source](main.tex)

This directory holds the manuscript (amsart, 18 pages): Theorem S′ and its proof, its
consequences (Corollary R, Do Duc's conditions, the square-free corollary, Kumar–Scholtz–Welch
`m = 1`, Arasu's list), the ramified regime (Lemma A, Theorems B and C), related work, the
formal-verification table and an appendix on quaternary sequences. The source files are
`main.tex`, `macros.tex`, `refs.bib` and `sections/*.tex`. The committed `main.pdf` is the
version that was mock-reviewed (see `../verification/mock-reviews/`).

## Build

You need a TeX Live (or MiKTeX) installation with `pdflatex`, `bibtex`, the AMS packages
(`amsart`, `amsmath`, `amssymb`, `amsthm`), `mathtools`, `geometry`, `booktabs`, `longtable`,
`xcolor`, `enumitem`, `hyperref`, `xurl` and `fancyvrb`. From the repository root:

```sh
bash paper/build.sh
```

The script runs `pdflatex`, `bibtex` and `pdflatex` twice more, all in `paper/build/`. It
fails on LaTeX errors and on undefined references or citations, warns on overfull boxes, and
copies the result to `paper/main.pdf`. Shell escape is disabled. No Lean build is needed to
typeset the paper. The title page uses `\date{\today}`, so the PDF changes with the build date.
Alternatively, `cd paper && latexmk -pdf main.tex` also works.

## Items left for the author

- `\author{}` in `main.tex` is empty (placeholder "Author information will be added in the
  final version"). Fill in names, affiliations and e-mail addresses.
- The "Use of AI tools" statement (`sections/07-statements.tex`) is a draft. Align it with the
  repository's AI attribution and with the target venue's policy.
- Section 5.3 ("Artifact and data availability", `sections/05-verification.tex`) still refers
  to the development branch of the openai/math fork. Point it at this repository and its
  release commit.
- The prior-art check against the paywalled references listed in the top-level README is
  pending (Leung–Chue–Zhao 2025 first).
