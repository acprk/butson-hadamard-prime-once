# Merged fix list after two mock reviews (R1-JCTA, R2-SIDMA), 2026-10-09

Both reviewers recommend **major revision**. Both found the mathematics correct:
- S/S′, Corollary R, Cor 5.5 (KSW), Cor 5.6, Lemma A, Theorem B and Theorem C were checked line by line.
- Lean `#print axioms` was re-run independently.
- Independent searches on non-cyclic groups and edge cases all returned 0, and the positive controls match.
- 2262/61/364, the LSZ "?" entries and the quaternary lists were reproduced exactly.

## Severe (required before any submission)
1. **Prior-art verification by reading full texts.** Both reviewers flag this.
   - Read ADM 2002, Ma 1996, Ma–Ng 2009, Pott LNM 1601 ch. 4, Schmidt LNM 1797, de Launey–Flannery, and especially **Leung–Chue–Zhao DCC 93 (2025)**. LCZ25 shows that cyclic BH of prime order are Fourier matrices, which covers H=1, and gives necessary conditions for order 2p; these may overlap S at n=2p.
   - Replace the inferential "three facts show experts did not know" argument in §2 with an actual literature check. Ideally, ask Schmidt, Leung or Do Duc directly. [Needs the user: institutional access and outreach.]
2. **Cite Mow's 1995 conjecture.** S proves part of its necessity direction. (R1)
3. **Restructure as a short paper of 8–12 pp.** Give the full proof of S′ in the introduction. Drop Part III, which has no full proofs. Either make Theorem C self-contained without depending on the unrefereed OpenAI 179 preprint, or split it off into a separate paper. Prove or remove the [179-Prop] claim about N≡2 mod 4. (R1+R2)
4. **Counting conventions.**
   - Write "excludes 2323 of the pairs listed in [DD19a]", not "closes".
   - Apply the same "previously excluded" deduction to the 2262 pairs as to the 61, or drop the "new" count.
   - "Only 3528 and 4900 left" must say "under the criteria we implemented". (R1+R2)
5. **Narrow the Lean tags.**
   - Table 1: separate formalized statements from computed consequences.
   - Cor 5.5 and 5.6 have only the general statement in Lean.
   - The "only 1,2,4,8,16" sentence relies on an Arasu remark.
   - Lemma 6.2 → "[Lean, n∈ℤ]".
   - Make the R Lean file location consistent. (R1+R2)
6. **Remove all TODOs, placeholder author names and internal paths.** Add an AI-use statement per the venue's policy. (R1+R2)

## Important
7. Corollary R actually implies **all** nonexistence results of LSZ23 §6; state this instead of only "the p∤n cases". (R1)
8. **F-value footnote.** Schmidt 1999 Def 3.1 is undefined for even m with q=2; use LS05 Def 2.6 or LS12 Def 2.10. Lemma 5.7 additionally excludes, in (1000, 10⁶], the lengths 1800, 3600, 6084, 12100, 12168, 14112 and 24200; list all seven. (R1)
9. **Publish the artifacts:** Lean code with commit hash, build log and axiom output, plus the computation scripts used for Cor 5.8 and the counts. (R1+R2)
10. Make Remark 4.5 ("both hypotheses necessary") precise. Add the non-cyclic search results (Z₃×Z₆ h=6, Z₂×Z₆ h=8, Z₂×Z₁₀ h=4,6, Z₂³×Z₃ h=4, p=2 with h odd) as evidence of sharpness and sanity. (R2)
11. Phrase the LS2012 Ex 3.2 footnote neutrally (already agreed).

## Minor
- Compress the abstract; move Cor 5.8 to an appendix; fix numbering references (the "Lemma 5.5" in internal notes is Lemma 5.7 in the PDF).

Full reports: release/review/R1-JCTA.txt, release/review/R2-SIDMA.txt.
