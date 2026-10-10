# Theorem E2: the family $n = 4qr$, closing $(84,21)$

**Status: single derivation plus exhaustive checks; not independently re-verified.** No peer review. Paper proof only.

**Nature.** A parallel extension of Theorem Q2 from $C_q$ to $C_q \times C_r$: the descent of Q2 is run once in each
direction, and each direction needs control of the valuations at the other prime, which is supplied by standard
decomposition-group (Turyn-type self-conjugacy or $\tau$-fixedness) conditions. The only new case, $\kappa = \pm 1$ with
$|S| = 2m/3$, is killed by $2$-self-conjugacy or, for $(84,21)$, by a finite classification plus Parseval. We record it
because it closes one entry of the list; it is not a new method. The genuinely hard entries $(60,15)$, $(60,45)$,
$(60,75)$ are not closed, and we give an explicit certificate that the method fails there.

## Notation

$q < r$ odd primes, $m = qr$, $h$ odd, $G = C_4 \times C_q \times C_r$, $D = \sum_y T^y C_y$ with $C_y \in \mathbb{Z}[\zeta_h][H]$,
$H = C_q \times C_r$, $DD^* = 4m$. As in Theorem Q2, $a = C_0 - C_2$, $b = C_1 - C_3$, $f = a + ib$, and
$F(\phi,\psi) := f(\phi\psi)$ for $\phi \in \widehat{C_q}$, $\psi \in \widehat{C_r}$. Let $M = \operatorname{lcm}(h, m)$,
$k = \mathbb{Q}(\zeta_M)$, $K = k(i) = \mathbb{Q}(\zeta_{4M})$, $\tau \in \mathrm{Gal}(K/k)$ with $\tau(i) = -i$, and $c$ complex
conjugation. For a prime $p$, $D_p \subset \mathrm{Gal}(K/\mathbb{Q})$ is its decomposition group (the same for all primes
above $p$, the group being abelian).

## Proposition 1 (one-direction descent)

**Proposition 1.** Assume $v_q(h) \le 1$ and ($\tau \in D_r$ or $c \in D_r$). Then $F(\phi,\psi)/F(1,\psi) \in k$ for all
$\phi, \psi$.

*Proof.* Fix $\psi$ and let $X = f_\psi \in \mathbb{Z}[\zeta_{4M}][C_q]$ be the image under $\psi$. Then $XX^* = 4m$ and
$v_{\mathfrak Q}(4m) = q - 1$ at each $\mathfrak Q \mid q$, since $q \parallel 4M$. By Lemma A, $u := X(\phi)/X(1)$ is a
$\mathfrak Q$-unit with residue $1$ at every $\mathfrak Q \mid q$. Primes above $2$ are $\tau$-fixed ($\tau$ lies in the
inertia group). For a prime $R \mid r$: if $\tau R = R$ then $v_R(\tau u) = v_R(u)$; if $cR = R$, then $|F|^2 = 4m$ gives
$v_R(F) = v_R(4m)/2$ for every character value, so $v_R(u) = 0$. Hence $\varepsilon = \tau(u)/u$ is a unit at every prime
with $|\varepsilon| = 1$ everywhere, so a root of unity; $\varepsilon \equiv 1 \bmod \mathfrak Q$ gives $q$-power order, so
$\varepsilon \in \mu_q \subset k$, $\tau(\varepsilon) = \varepsilon = \varepsilon^{-1}$, and $\varepsilon = 1$. $\square$

With "no other odd prime" in place of $r$ this is Step 2 of Theorem Q2; the new point is only the condition on $D_r$.

## Theorem E2

**Theorem E2.** Let $q < r$ be odd primes, $m = qr$, $h$ odd with $v_q(h) \le 1$ and $v_r(h) \le 1$. Assume, in
$\mathrm{Gal}(\mathbb{Q}(\zeta_{4\operatorname{lcm}(h,m)})/\mathbb{Q})$,

$$\text{(D}_q\text{)}\ \ \tau \in D_r \text{ or } c \in D_r,\qquad \text{(D}_r\text{)}\ \ \tau \in D_q \text{ or } c \in D_q,$$

that $5 \nmid m$, and that either $3 \nmid m$, or $-1 \in \langle 2 \rangle \subset (\mathbb{Z}/\operatorname{lcm}(h,m))^*$, or
$(m,h) = (21,21)$. Then there is no $\mathrm{BH}(C_4 \times C_q \times C_r, h)$, i.e. no perfect sequence of length $4qr$
over $\mu_h$.

*Proof.* **Step 1.** By Proposition 1 in both directions (the $r$-direction is Proposition 1 applied to $f_\phi \in
\mathcal O[C_r]$),
$f(\phi\psi)/f(1) = [F(\phi,\psi)/F(\phi,1)]\cdot[F(\phi,1)/F(1,1)] \in k$ for all characters.

**Step 2.** This is Steps 3–5 of Theorem Q2, unchanged: $a = \kappa b$ in $k[H]$ with $\kappa \ne 0$ a scalar. $b = 0$
is impossible because the identity coefficient of $aa^* = 4m$ is a sum of $m$ terms $|C_0 - C_2|^2 < 4$ ($h$ odd). So
$\kappa$ is totally real and $bb^* = 4m/(1+\kappa^2)$.

**Step 3.** Step 6 of Theorem Q2, unchanged (it is columnwise and uses only $h$ odd): off $S = \operatorname{supp} b$ the
columns are $(u,v,u,v)$; on $S$ they are $\varphi_w(z^d, z^{d'}, z^{-d}, z^{-d'})$ with a common Lemma-K class, and
$\sum_{w\in S}(4 - \Sigma_4(w)) = 4m$.

**Step 4 (generic $\kappa \ne \pm 1$).** $\Sigma_4$ is the same for all $w \in S$, hence rational, hence $-1$ or $-2$.
$\Sigma_4 = -1$ forces $5s = 4m$, excluded by $5 \nmid m$. $\Sigma_4 = -2$ forces $z^{2d}, z^{2d'}$ of order $3$, so
$\kappa = \pm 1$, a contradiction.

**Step 5 ($\kappa = \pm 1$; without loss of generality $\kappa = 1$ via $D \mapsto TD$).** Then $d'_w = d_w$, so the
columns are $(c, c, c\,\omega_w, c\,\omega_w)$ on $S$ and $(u, u\nu_w, u, u\nu_w)$ off $S$. The Galois-average argument
of Theorem Q2, with $m$ in place of $q$, gives $s = 2m/3$, and every $\omega_w$ and $\nu_w$ has order exactly $3$. In
particular $3 \mid m$.
- (a) If $-1 \in \langle 2 \rangle$ modulo $\operatorname{lcm}(h,m)$: $f = (1+i)a$, so $aa^* = 2m$. Every prime above $2$ in
  $\mathbb{Q}(\zeta_{\operatorname{lcm}(h,m)})$ is unramified and self-conjugate, so $2v_P(a(\chi)) = v_P(2m) = 1$, which is
  impossible.
- (b) $(m,h) = (21,21)$. Put $A = a/(1-\omega)$ and $B = e_-/(2(1-\omega))$, supported on $S$ and $T = H \setminus S$
  respectively, with all entries in $\mu_{42}$, $AA^* = 14$, $BB^* = 7$ and $|T| = 7$.
  *Fact (exhaustive, exact arithmetic):* a $7$-subset $T \subset \mathbb{Z}_{21}$ carries a $\mu_{42}$-weighing $B$ with
  $BB^* = 7$ only if $T$ is a coset of the subgroup of order $7$. (Of the 22 support classes, up to translation and
  multiplier, that survive the necessary condition "no nonzero difference occurs exactly once", 21 have no solution and
  the coset has 42 normalised solutions. An independent run over all 1303 such supports containing $0$, without
  multiplier reduction, finds solutions only for $\{0,3,\dots,18\}$.)
  So $S$ is the union of the other two cosets: $A = A_1 g + A_2 g^2$ with $A_1, A_2 \in \mathbb{Z}[\mu_{42}][C_7]$, each
  with $7$ entries that are roots of unity. $AA^* = 14$ gives $A_1A_2^* = 0$ and $A_1A_1^* + A_2A_2^* = 14$. So for each
  $\psi \in \widehat{C_7}$ one of $A_1(\psi), A_2(\psi)$ vanishes and $|A_1(\psi)|^2 \in \{0, 14\}$. Parseval gives
  $\sum_\psi |A_1(\psi)|^2 = 7 \cdot 7 = 49$, not a multiple of $14$. Contradiction. $\square$

## Entries closed

- **Do Duc's open list ($n, h \le 100$):** $(84,21)$ only. The $q = 3$ direction holds because the primes above $7$ are
  $\tau$-fixed ($7 \equiv 3 \bmod 4$, $7 \equiv 1 \bmod 3$); the $r = 7$ direction holds because $3$ is self-conjugate
  modulo $28$ ($3^3 \equiv -1 \bmod 28$).
- **Beyond $100$, with $qr \mid h$** (`family.py`, $n \le 1000$, $h \le 300$): $(132,33)$, $(228,57)$, $(516,129)$,
  $(708,177)$, $(804,201)$, $(996,249)$, $(308,77)$, $(532,133)$, $(644,161)$, $(868,217)$, $(836,209)$. Allowing $h$ not
  divisible by $qr$, Theorem E2 applies to 116 pairs in that range, most of which are probably excluded by classical
  criteria; we have not checked them against the literature.
- **Not closed:** $(60,15)$, $(60,45)$, $(60,75)$, $(84,63)$.

## Where the method fails: $(60,15)$

In $K = \mathbb{Q}(\zeta_{60})$ the primes $3$ and $5$ each split into two primes $P$, $cP = \tau P$: $c\tau \in D_p$ but
$\tau, c \notin D_p$. So the valuations of the two-term ratio at the other prime are unconstrained. An explicit
certificate (`fake60.sage`): $X = x_0 + x_1 g + x_2 g^2 \in \mathbb{Z}[\zeta_{60}][C_3]$ with

$$x_0 = -2\zeta^{11} + 4\zeta,\quad x_1 = -4\zeta^{14} + 2\zeta^{11} + 4\zeta^{10} + 4\zeta^{8} + 2\zeta^{6} - 4\zeta^{2} + 2\zeta - 4,\quad x_2 = 2\zeta^{14} - 4\zeta^{11} - 2\zeta^{10} - 2\zeta^{8} + 2\zeta^{6} + 2\zeta^{2} + 2\zeta + 2$$

($\zeta = \zeta_{60}$) satisfies $XX^* = 60$ exactly, $v_R(X(1)) = 0$ and $v_R(X(\chi)) = 4$ at a prime $R \mid 5$, and
$X(\chi)/X(1) \notin \mathbb{Q}(\zeta_{15})$; $\tau(u)/u$ is not a root of unity. Then $f := X \otimes \delta_{C_5}$ satisfies
$ff^* = 60$, Lemma A at $3$ and at $5$, and the cross-ratio descent, but its two-term ratio is not in $k$. So every
hypothesis the descent uses holds and its conclusion fails. (Its coefficients have absolute value at most about $7.7$ in
every embedding, below the bound $20$ for a projection of a genuine $D$, so size does not exclude it.) $(60,45)$ and
$(60,75)$ have the same structure; for $(60,45)$ Lemma A at $3$ is also lost ($9 \mid h$).

## Checks and reproduction

Run from `results/q2-series/scripts/`.

| Check | Command | Result | Time |
| --- | --- | --- | --- |
| decomposition-group conditions for $(60,15)$, $(60,45)$, $(60,75)$, $(84,21)$, $(84,63)$ | `python3 decomp.py` | both directions hold only for $(84,21)$ | < 1 s |
| family of entries satisfying Theorem E2 | `python3 family.py` | list above | 73 s |
| the 22 support classes for $(m,h) = (21,21)$ | `sh run_wexact.sh reps` | only $\{0,3,6,9,12,15,18\}$ has solutions (42) | 16.5 min (almost all on the coset support) |
| all 1303 supports containing $0$ | `sh run_wexact.sh all` | only $\{0,3,\dots,18\}$ has solutions (42) | 61 min |
| reduction table used by `wexact.c` | `python3 gen_phi42.py \| diff - phi42.h` | identical | < 1 s |
| failure certificate at $(60,15)$ | `sage fake60.sage` | 4 objects found, each with $XX^* = 60$ and ratio not in $k$ | 8 min (class number of $\mathbb{Q}(\zeta_{60})$, `proof=False`) |
| entries closed, across the whole list | `python3 closed_entries.py` | $(84,21)$ | < 1 s |

`run_wexact.sh` compiles `wexact.c` (needs a C compiler) and runs it on every support from `supports.py` /
`supports_all.py`. `wexact.c` enumerates $B : T \to \mu_{42}$ with $B(T_0) = 1$ and tests each partial difference sum for
exact vanishing in $\mathbb{Z}[\zeta_{42}]$ via the table `phi42.h`.
