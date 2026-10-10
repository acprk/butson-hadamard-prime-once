# Theorem Q2′: no $\mathrm{BH}(\mathbb{Z}_{4q},h)$ for $h$ odd

**Status: single derivation plus exhaustive checks; not independently re-verified.** No peer review. Paper proof only.

**Nature.** Theorem Q2′ is a degree-bound extension of Lemma A. The only change to the proof of Theorem Q2 is Lemma A′
below, which allows the coefficient ring to be ramified at $p$; the degree bound $\deg c_i \le i$ of Lemma A becomes
$\deg c_i \le \lfloor i/Q \rfloor$. Steps 2–6 of Theorem Q2 are unchanged. We regard it as a bookkeeping corollary.

## Lemma A′ (ramified coefficients)

**Lemma A′.** Let $p$ be an odd prime, $L/\mathbb{Q}_p$ a finite extension with $\zeta_p \in L$, $\mathcal O = \mathcal O_L$,
$\pi$ a uniformiser, $e = e(L/\mathbb{Q}_p)$, $\mathbb F$ the residue field, $y = \zeta_p - 1$ and
$Q := v_\pi(y) = e/(p-1)$. Let $F, G \in \mathcal O[C_p]$ with $FG = n$ in $\mathcal O[C_p]$, where $n \in \mathcal O$ and
$v_\pi(n) = e$ (that is, $v_p(n) = 1$). Put $F_j = F(\zeta_p^j)$, $G_j = G(\zeta_p^j)$ for $j \in \mathbb F_p$. Then
$v_\pi(F_j)$ does not depend on $j$, and $F_j/F_0 \equiv 1 \pmod \pi$ for all $j$.

Lemma A of the paper is the case $Q = 1$ ($p$ unramified in the coefficients). The Lean statement `lemmaA` and the
underlying `ramified_comparison_core` assume $Q = 1$ and do not cover Lemma A′.

*Proof.* Let $W$ be the ring of integers of the maximal unramified subextension. Then $\mathcal O = W[\pi]$ and the
Eisenstein polynomial of $\pi$ reduces to $X^e$, so $\mathcal O/p\mathcal O \cong \mathbb F[\pi]/(\pi^e)$ as
$\mathbb F$-algebras. Write $\delta_i : \mathcal O/p\mathcal O \to \mathbb F$ ($0 \le i < e$) for the $\mathbb F$-linear
digit maps. For $x \in \mathcal O$ with $v_\pi(x) = \alpha < e$ one has $\delta_i(x) = 0$ for $i < \alpha$, and
$\delta_\alpha(x)$ is the residue of $x/\pi^\alpha$, which is nonzero; if all digits vanish then $v_\pi(x) \ge e$.

(i) Evaluation is a ring map, so $F_jG_j = n$ and $a(j) + b(j) = e$ with $a(j) = v_\pi(F_j)$, $b(j) = v_\pi(G_j)$.

(ii) Write $F = \sum_a u_a g^a$. Then $F_j = \sum_a u_a (1+y)^{m}$ with $m = (ja \bmod p) \in [0, p-1]$. Modulo $p$,
$y^l \equiv 0$ for $l \ge p-1$ because $v_\pi(y^l) = Ql \ge e$. For $l < p$, $\binom{m}{l} \bmod p = B_l(ja)$ with
$B_l(X) = X(X-1)\cdots(X-l+1)/l! \in \mathbb F_p[X]$. Also $\delta_i(u_a y^l) = 0$ if $Ql > i$. Hence

$$\delta_i(F_j) = c_i(j),\qquad c_i(T) := \sum_a \sum_{l \le \lfloor i/Q \rfloor} \delta_i(u_a y^l)\, B_l(aT) \in \mathbb F[T],\qquad \deg c_i \le \lfloor i/Q \rfloor .$$

This is the only change from Lemma A, where the bound is $\deg c_i \le i$. The same holds for $G$ with digit polynomials
$c^*_i$. Note $\lfloor i/Q \rfloor \le p - 2$ for $i < e$.

(iii) Boundary cases. If $a(j) = e$ for some $j$, then $\min_j b = 0$. Since $\deg c^*_0 = 0$, $c^*_0$ is a constant,
nonzero because some $G_j$ is a unit; so every $G_j$ is a unit, $b \equiv 0$, $a \equiv e$, and
$F_j/F_0 = G_0/G_j \equiv 1 \pmod\pi$. The case $b(j) = e$ is symmetric.

(iv) Otherwise $\alpha := \min a < e$ and $\beta := \min b < e$, and $\alpha + \beta \le e$. For $i < \alpha$, $c_i$
vanishes on all of $\mathbb F_p$ and has degree $\le p-2$, so $c_i = 0$. Thus $a(j) > \alpha$ iff $c_\alpha(j) = 0$, and
$c_\alpha \ne 0$, so at most $\lfloor \alpha/Q \rfloor$ values of $j$ have $a(j) > \alpha$. Likewise at most
$\lfloor \beta/Q \rfloor$ have $b(j) > \beta$. Since $\lfloor \alpha/Q \rfloor + \lfloor \beta/Q \rfloor \le \lfloor e/Q \rfloor
= p - 1 < p$, some $j_0$ has $a(j_0) = \alpha$ and $b(j_0) = \beta$. So $\alpha + \beta = e$, and $a \equiv \alpha$,
$b \equiv \beta$.

(v) The residue of $F_j/\pi^\alpha$ is $c_\alpha(j)$ and that of $G_j/\pi^\beta$ is $c^*_\beta(j)$; their product is the
residue of $n/\pi^e$, the same for all $j$. The polynomial $c_\alpha c^*_\beta$ has degree
$\le \lfloor\alpha/Q\rfloor + \lfloor\beta/Q\rfloor \le p-1$ and takes one value at $p$ points, so it is constant. Since
$\mathbb F[T]$ is a domain, $c_\alpha$ is constant, i.e. $F_j/F_0 \equiv 1 \pmod \pi$. $\square$

*Sharpness.* The hypothesis $v_p(n) = 1$ is still needed: with $v_3(n) = 2$ the enumeration below finds 81 of 108
(resp. 405 of 432) solutions violating the conclusion.

*Global use.* With $K = \mathbb{Q}(\zeta_{4h})$, $q^a \parallel h$ ($a \ge 1$) and $\mathfrak P \mid q$, take
$L = K_{\mathfrak P}$. Then $e = q^{a-1}(q-1)$, $Q = q^{a-1}$ and $v_{\mathfrak P}(4q) = e$.

## Theorem Q2′

**Theorem Q2′.** Let $q$ be an odd prime and $h$ odd. Then there is no perfect sequence of length $4q$ over $\mu_h$,
i.e. no $\mathrm{BH}(C_4 \times C_q, h)$.

*Proof.* If $q \nmid h$, this is Theorem S. Let $q^a \parallel h$ with $a \ge 1$. Run the proof of Theorem Q2
([theorem-q2.md](theorem-q2.md)) verbatim, with Lemma A′ in place of Lemma A in Step 1: $f = a + ib \in
\mathbb{Z}[\zeta_{4h}][C_q]$, $ff^* = 4q$ and $v_{\mathfrak P}(4q) = e(\mathfrak P \mid q)$ at every $\mathfrak P \mid q$, so
$r_\chi = f(\chi)/f(1)$ is a $\mathfrak P$-unit with residue $1$. The remaining steps were re-read for any use of
$q \parallel h$:
- Step 2: $\varepsilon = \tau(r)/r$ is a root of unity $\equiv 1 \pmod{\mathfrak P}$, so of $q$-power order, so
  $\varepsilon \in \mu_{q^a} \subset k = \mathbb{Q}(\zeta_h)$ (because $q^a \parallel 4h$); then
  $\tau(\varepsilon) = \varepsilon = \varepsilon^{-1}$ and odd order give $\varepsilon = 1$.
- Steps 3–5 use only $K = k \oplus ik$ ($h$ odd) and the coefficient identities.
- Step 6, Lemma K, the rational values of $\Sigma_4$, the case $\kappa = \pm 1$ and the cases $q = 3$, $q = 5$ hold for every
  odd $h$. (The Galois-average bound $2\mu(m)/\varphi(m) \in [-1, 1/4]$ holds for every odd $m > 1$, including $m = q^2$,
  where the value is $0$.)

Nothing else used $q \parallel h$. $\square$

**Why vanishing-sum descent does not already give this.** For $(28,49)$ and $(20,75)$ the classical reduction of $h$ to a
smaller $h_1$ through vanishing sums of roots of unity does not apply. A collapse $\mu_{q^a} \to \mu_q$ is
$x \mapsto x^{q^{a-1}}$ up to a unit, and its kernel contains $\mu_q$. For $h = 49$, by Lam–Leung every nonnegative
vanishing sum of $49$-th roots of unity is a union of cosets $z\mu_7$, and $x \mapsto x^7$ sends each such coset to $7z^7
\ne 0$. For $h = 75$, $\Phi_{25}(x) = \Phi_5(x^5)$ is irreducible over $\mathbb{Q}(\zeta_3)$, and $20 = 3\cdot 5 + 5 \cdot 1$
admits mixed vanishing sums of length $20$.

## Entries of Do Duc's open list closed

Beyond Theorem Q2: $(20,75)$ and $(28,49)$. ($(12,45)$ and $(12,63)$ are also covered but were already excluded by
vanishing-sum descent.)

## Checks and reproduction

Run from `results/q2-series/scripts/`. Sage scripts load `norm_elements.sage` from their own directory.

| Check | Command | Result | Time |
| --- | --- | --- | --- |
| Lemma A′, complete enumeration of all $F$ with $FF^* = n$ in $\mathcal O[C_3]$, $\mathcal O = \mathbb{Z}[\zeta_{3d}]$ with $3 \mid d$ | `sage lemmaA_ram_enum.sage 3 3 3` (args $p\ d\ n$; also `3 3 12`, `3 3 21`, `3 3 57`, `3 9 3`, `3 9 12`, `3 9 57`, `3 12 12`, `3 12 39`) | 0 violations (3 to 1536 solutions per case) | 2–15 s each |
| larger cases | `sage lemmaA_ram_enum.sage 3 12 111` (also `3 12 219`) | 0 violations, 262146 solutions | 31 min (`3 12 111`, rerun); `3 12 219` not rerun |
| negative controls ($v_3(n) = 2$) | `sage lemmaA_ram_enum.sage 3 3 9 1 neg`, `sage lemmaA_ram_enum.sage 3 12 36 1 neg` | 81/108 and 405/432 violations | 3–4 s |
| structured search for the target entries | `python3 structured.py 7 49`; `python3 structured.py 5 75` | $(28,49)$: 0 survivors; $(20,75)$: 4 survivors ($\kappa = \pm\phi^{\pm1}$ with $\phi$ the golden ratio, $s = 4$), 24000 completions, 0 perfect | 80 s; 43 min, 3.8 GB |
| exhaustive, no theory used | `./bhcol 3 9`, `./bhcol 3 27` | 0 sequences | < 3 s |
| control on genuine objects with $q^2 \mid h$, $h$ even | `./bhcol 3 18 print 2>/dev/null` (lists the 36 orbit representatives in `bh_12_18_reps.txt`), then `sage control_chain.sage` | Lemma A′, Step 2, Step 3 hold on 36/36; all 36 have $a = 0$, i.e. the chain breaks exactly at Step 4 ($-1 \in \mu_{18}$) | 1 s |

Notes. `lemmaA_ram_enum.sage` enumerates the complete list of norm-$n$ elements (ideal enumeration plus unit
normalisation) and re-verifies every hit exactly. The $p\ d\ n$ arguments correspond to $N = pd \in \{9, 27, 36\}$, so
$e(\mathfrak P \mid 3) \in \{6, 18\}$. Of the two cases with 262146 solutions, `3 12 111` was rerun for this release (31 minutes on one core);
`3 12 219` was not rerun. `python3 structured.py 5 75` enumerates $75^4 \approx 3.2\times10^7$ column
types; it was rerun for this release (43 minutes, peak memory 3.8 GB).
