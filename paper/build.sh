#!/usr/bin/env bash
# Build paper/main.pdf from the LaTeX sources (pdflatex + bibtex, amsart, amsalpha).
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

mkdir -p build
run_pdflatex() {
  if ! pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error \
      -file-line-error -output-directory=build main.tex >"build/pass-$1.txt"; then
    cat "build/pass-$1.txt" >&2
    exit 1
  fi
}

run_pdflatex 1
# bibtex runs inside build/; point it at the .bib and .bst search paths here.
(cd build && BIBINPUTS="..:${BIBINPUTS:-}" bibtex main >bibtex.txt) || {
  cat build/bibtex.txt >&2
  exit 1
}
run_pdflatex 2
run_pdflatex 3

if grep -Eq 'LaTeX Warning: (Citation|Reference).*undefined|There were undefined references|Rerun to get cross-references right' build/main.log; then
  grep -E 'undefined|Rerun to get cross-references right' build/main.log >&2
  exit 1
fi
if grep -q 'Overfull' build/main.log; then
  printf '%s\n' 'warning: overfull boxes in build/main.log' >&2
fi
cp build/main.pdf main.pdf
printf 'Built paper/main.pdf\n'
