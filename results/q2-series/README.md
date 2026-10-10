# The Q2 series: $\nu_2(n) = 2$, $h$ odd

These results concern group-invariant Butson Hadamard matrices $\mathrm{BH}(G,h)$ (equivalently, perfect sequences over
$\mu_h$ when $G$ is cyclic) whose Sylow $2$-subgroup is $C_4$ and $h$ is odd. They are the case $q = 2$ of the question
whether a cyclic Sylow $q$-subgroup of order $q^2$ with $q \nmid h$ rules out $\mathrm{BH}(G,h)$ (see
[../obstructions/README.md](../obstructions/README.md)). The main paper's Theorem S′ does not apply to the entries
closed here: $2^2 \mid n$, and every odd prime dividing $n$ exactly once (if any) divides $h$, so it is ramified.

**Caveats.** No peer review. Paper proofs only; none of these theorems is formalized in Lean. "Closed" means "excluded
by the theorem", and "open" means "not excluded by any criterion we implemented"; we have not completed a literature
check for these entries (see the prior-art caveat in the [top-level README](../../README.md#status-and-caveats)).

| Result | Statement | Status | Nature |
| --- | --- | --- | --- |
| [Theorem Q2](theorem-q2.md) | no $\mathrm{BH}(\mathbb{Z}_{4q},h)$, $q$ odd prime, $h$ odd, $q^2 \nmid h$ | independently verified | Lemma A + Galois descent + new elementary endgame (Lemma K) |
| [Theorem Q2′](theorem-q2-prime.md) | same without $q^2 \nmid h$ | single derivation + exhaustive checks | degree-bound extension of Lemma A (Lemma A′) |
| [Theorem E1](theorem-e1.md) | no $\mathrm{BH}(\mathbb{Z}_{4q^2},h)$, $h$ odd, $q^2 \nmid h$, condition (W) | single derivation + exhaustive checks | Schmidt field descent + Leung–Schmidt (2011) concentration/Parseval template + new endgame |
| [Theorem E2](theorem-e2.md) | no $\mathrm{BH}(\mathbb{Z}_{4qr},h)$ under decomposition-group conditions | single derivation + exhaustive checks | parallel extension of Q2 |

## Entries closed

The reference list is Do Duc's list of open pairs $(n,h)$, $n, h \le 100$ (2019, Remark 3.13), transcribed in
[`computations/count2262/DoDuc_BH_open_cases.txt`](../../computations/count2262/DoDuc_BH_open_cases.txt). Before the
Q2 series, 81 entries with a cyclic Sylow $q$-subgroup of order $q^2$ and $q \nmid h$ were not excluded by any criterion
we implemented; they are listed, with that caveat, in
[`data/remaining_before_q2_series.json`](data/remaining_before_q2_series.json). (Most of those earlier criteria are not part
of this release.)

The Q2 series closes **18** entries:

| Theorem | Entries |
| --- | --- |
| Q2 | $(20,45)$, $(28,7)$, $(28,21)$, $(28,63)$, $(52,39)$, $(68,51)$, $(92,23)$, $(92,69)$ |
| Q2′ | $(20,75)$, $(28,49)$ |
| E1 | $(36,15)$, $(36,75)$, $(100,15)$, $(100,35)$, $(100,45)$, $(100,85)$, $(100,95)$ |
| E2 | $(84,21)$ |

Seventeen of these are among the 81. The eighteenth, $(28,7)$, had been excluded earlier only by a GRH-conditional
column computation; Theorem Q2 makes it unconditional. Theorem Q2 also covers $(28,35)$, $(28,77)$, $(28,91)$ directly;
these had been excluded only conditionally on $(28,7)$, through vanishing-sum descent, and are not counted among the 18.

After the Q2 series, **64** of the 81 entries remain; they are listed in
[`../remaining-open-cases.json`](../remaining-open-cases.json) (by $q$: 43 with $q = 3$ only, 9 with $q = 2$ only,
7 with $q = 5$ only, 2 with $q \in \{2,3\}$, 3 with $q \in \{2,5\}$).

To recompute the closed list from the hypotheses of the four theorems and regenerate `../remaining-open-cases.json`
(stdlib Python only, < 1 s):

```sh
cd results/q2-series/scripts && python3 closed_entries.py
```

It tests the hypotheses of Q2, Q2′, E1 and E2 on every entry of the Do Duc list (127 entries satisfy one of them; most
were already excluded by other criteria), intersects with the snapshot of 81, and checks that the result is the 17
entries above plus $(28,7)$.

## Scripts

All scripts are in [`scripts/`](scripts/) and use paths relative to their own location. Tested on Linux with Python
3.10 (`numpy` 2.2, `mpmath` 1.3), SageMath 9.5, PARI/GP 2.13 and gcc 9.5. The commands, results and running times are listed in
each theorem's file.

| Script | Used for |
| --- | --- |
| `closed_entries.py`, `decomp.py` | closed entries and remaining list; decomposition-group conditions (E2) |
| `lemmaK_check.py`, `sigma4.py` | Lemma K and the rational values of $\Sigma_4$ (Q2) |
| `bhcol.c` | exhaustive search for $\mathrm{BH}(\mathbb{Z}_{4q},h)$, no theory used (Q2, Q2′) |
| `structured.py` | structured search using only Steps 1–3, 5 of Q2 (Q2, Q2′) |
| `lemmaA_ram_enum.sage`, `norm_elements.sage` | complete enumeration test of Lemma A′ (Q2′) |
| `control_chain.sage`, `bh_12_18_reps.txt` | Q2′ steps on the 36 genuine $\mathrm{BH}(\mathbb{Z}_{12},18)$ orbit representatives |
| `blockcheck.c`, `blockcheck_poscontrol.py` | brute force of the combinatorial half of E1 for $n = 36$, with positive control |
| `e1_endgame_controls.py`, `q2_failure_n36.py`, `q2_failure_n36_exact.sage` | E1 controls; failure of Q2's descent at $n = 36$ |
| `family.py` | entries satisfying E2 for $n \le 1000$, $h \le 300$ |
| `supports.py`, `supports_all.py`, `wexact.c`, `phi42.h`, `gen_phi42.py`, `run_wexact.sh` | the $(21,21)$ weighing classification in E2 |
| `fake60.sage` | failure certificate for the descent at $(60,15)$ |

Every listed command was rerun for this release except `sage lemmaA_ram_enum.sage 3 12 219` (the companion case
`3 12 111` took 31 minutes). The slowest reruns were `structured.py 5 75` (43 min, 3.8 GB), `run_wexact.sh all` (61 min)
and `fake60.sage` (8 min).
