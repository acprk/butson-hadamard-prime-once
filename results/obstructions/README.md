# Obstructions for $\nu_q \ge 2$

This note collects precise negative results about methods for the following problem.

> **Conjecture S2.** Let $G$ be a finite abelian group, $q$ a prime, and suppose the Sylow $q$-subgroup of $G$ is
> cyclic of order $q^a$ with $a \ge 2$. If $q \nmid h$, there is no $\mathrm{BH}(G,h)$, i.e. no $a : G \to \mu_h$ with
> $\sum_x a(x+s)\overline{a(x)} = 0$ for all $s \ne 0$.

The main target is $a = 2$, $G = C_{q^2} \times H$ with $q \nmid |H|$. Conjecture S2 is the cyclic-Sylow case
$\nu_q(n) \ge 2$ of Do Duc's Conjecture 3.1(i); Theorem S′ of the paper is the case $a = 1$. The cyclicity hypothesis
is essential: for $q \nmid h$, Do Duc (arXiv:1903.09824, Theorem 4.3) constructs genuine $\mathrm{BH}(C_q \times C_q, h)$
(for example 216 objects $\mathrm{BH}(C_3 \times C_3, 10)$), all of whose character values are $q$ times a root of unity.
Any argument that does not use cyclicity of the Sylow subgroup must fail on these objects.

Each item below gives a statement, a proof or a proof sketch (marked as such), and what it rules out. **Status:** these
are single derivations with computer checks; they have not been independently re-verified, and there is no peer review.
They are recorded as obstructions, not as results about Butson matrices.

Throughout, $G = C_{q^2} \times H$, $m = |H|$, $q \nmid m$, $q \nmid h$, $L = \operatorname{lcm}(h, \exp H)$,
$\mathcal O = \mathbb{Z}[\zeta_L]$, $K = qC_{q^2}$ (the subgroup of order $q$), and $D = \sum_g a(g)\,g \in
\mathbb{Z}[\zeta_h][G]$ with $DD^* = |G|$.

## 0. A sufficient divisibility condition

**Proposition 0.** If there is a character $\psi$ of $C_{q^2}$ of order $q^2$ such that $q \mid (\psi \times \phi)(D)$
for every $\phi \in \widehat H$, then $D$ cannot be perfect with unimodular coefficients. Hence the divisibility
"$q \mid \chi(D)$ for all $\chi$ of order divisible by $q^2$" would prove Conjecture S2 for $a = 2$.

*Proof.* Since $q \nmid L$, $\Phi_{q^2}(T) = 1 + T^q + \dots + T^{q(q-1)}$ is irreducible over $\mathbb{Q}(\zeta_L)$, and
it is the element $N_K = \sum_{k \in K} k$ of $\mathcal O[C_{q^2}]$. For $X_\phi = \phi(D) \in \mathcal O[C_{q^2}]$,
$q \mid \psi(X_\phi)$ means $X_\phi \in (q, N_K)$, i.e. the coefficients satisfy $x_c \equiv x_{c+q} \pmod q$. Writing
$D = \sum_c g^c D_c$ with $D_c \in \mathbb{Z}[\zeta_h][H]$, this says $\phi(D_c - D_{c+q}) \in q\mathcal O$ for all $\phi$;
since $m$ is a unit mod $q$, Fourier inversion gives $D_c - D_{c+q} \in q\mathbb{Z}[\zeta_h][H]$. Each coefficient is a
difference of two elements of $\mu_h$, and $\zeta - \zeta'$ is divisible by $q$ only if $\zeta = \zeta'$ (as $q \nmid h$).
So $D = N_K D'$, and $\chi(D) = 0$ for every $\chi$ nontrivial on $K$, contradicting $|\chi(D)|^2 = |G|$. $\square$

This is a standard argument in the spirit of Ma's lemma. Cyclicity enters through $\Phi_{q^2} = N_K$, and $q \nmid h$
through the last step.

## 1. Integral "fake" perfect elements

**Theorem 1.** For each of the six pairs $(n,h) = (72,8)$, $(45,35)$, $(99,77)$, $(100,44)$, $(90,20)$, $(63,91)$, with
$G = C_{q^2} \times C_m$, $n = q^2 m$, there is $D \in \mathbb{Z}[\zeta_h][G]$ with $DD^* = |G|$ **exactly**, such that
$q \nmid \chi(D)$ for **every** character $\chi$ whose restriction to $C_{q^2}$ has order $q^2$:

| $(n,h)$ | $q$ | $m$ | $D$ |
| --- | --- | --- | --- |
| $(72,8)$ | 3 | 8 | $E''(T^3) \otimes B$, where $E'' = \sum_{x \in \mathbb F_9^*}\omega(x)[\operatorname{Tr} x] + N_{C_3} = [1,\ -(\zeta_8+\zeta_8^3),\ 2+\zeta_8+\zeta_8^3] \in \mathbb{Z}[\zeta_8][C_3]$ ($\omega$ a character of $\mathbb F_9^*$ of order 8) and $B = [1,1,1,i,-1,1,-1,i]$ is a perfect quaternary sequence of length 8 |
| $(45,35)$ | 3 | 5 | $\gamma\,[0] \otimes \mathrm{Chu}_5$, $\gamma = (1+\sqrt{-35})/2$ |
| $(99,77)$ | 3 | 11 | $\gamma\,[0] \otimes \mathrm{Chu}_{11}$, $\gamma = ((1+\sqrt{-11})/2)^2$ |
| $(100,44)$ | 5 | 4 | $\gamma\,[0] \otimes [1,1,1,-1]$, $\gamma = ((3+\sqrt{-11})/2)^2$ |
| $(90,20)$ | 3 | 10 | $\gamma\,[0] \otimes \mathrm{Chu}_{10}$, $\gamma = 2 + \sqrt{-5}$ |
| $(63,91)$ | 3 | 7 | $\gamma\,[0] \otimes \mathrm{Chu}_{7}$, $\gamma = 2\zeta^{10}+2\zeta^9+2\zeta^7+\zeta^6+2\zeta^5+\zeta^4+2\zeta^3+2\zeta^2+\zeta+1$, $\zeta = \zeta_{13}$ |

In the last five rows $\gamma\bar\gamma = q^2$ and $\gamma[0]$ is supported on the identity of $C_{q^2}$. In the first
row, $E''$ takes the value $3$ at the trivial character of $C_3$ and a Gauss sum of absolute value $3$ at the others, so
$E''(T^3)E''(T^3)^* = 9$ in $\mathbb{Z}[\zeta_8][C_9]$; at the two primes of $\mathbb{Q}(\zeta_{72})$ above $3$ its
order-9 character values have valuations $(3,9)$ instead of the "uniform" $(6,6)$.

*Proof.* By exact computation: `scripts/fakes.gp` builds each $D$, checks $DD^* = |G|$ in $\mathbb{Z}[\zeta_h][G]$, and
checks for every order-$q^2$ character that some power-basis coefficient of $\chi(D) \in \mathbb{Z}[\zeta_N]$ is not
divisible by $q$. $\square$

**What it rules out.** Every one of these $D$ is integral, satisfies $DD^* = |G|$, has character values with the right
absolute values and Galois behaviour, and has integral partial and coset Fourier sums. So no argument whose inputs are
only (a) the ideals $(\chi(D))$ and their Stickelberger-type factorisation, (b) Galois equivariance, (c)
$\chi(D)\overline{\chi(D)} = |G|$, and (d) integrality of $D$ and of its partial/coset Fourier sums, can prove the
divisibility of Proposition 0. The missing input is unimodularity of the coefficients, which is not an ideal-level datum.
The fakes do violate single-coset Parseval (their support lies in one coset of $K \times H$), which is the archimedean
shadow of unimodularity used in Theorem S and in the Schmidt/Leung–Schmidt descent template. For every odd $q$
occurring in the remaining list below, $q$ is not self-conjugate modulo $h$ (direct check), so the scalar construction is
not excluded by self-conjugacy; it requires a suitable $\gamma$, which existed in all six cases tried.

## 2. Digit comparison carries no information when $q \nmid h$

**Proposition D1 (the twist is Galois).** Let $X \in \mathcal O[C_{q^2}]$ (for instance $X = \phi(D)$). For
$j \in (\mathbb{Z}/q^2)^*$ let $\tau_j \in \mathrm{Gal}(\mathbb{Q}(\zeta_{Lq^2})/\mathbb{Q}(\zeta_L))$ be the element with
$\tau_j(\zeta_{q^2}) = \zeta_{q^2}^j$ (it exists because $q \nmid L$). Then for every $k$,

$$X(\zeta_{q^2}^{kj}) = \tau_j\bigl(X(\zeta_{q^2}^{k})\bigr).$$

*Proof.* $\tau_j$ fixes the coefficients of $X$, which lie in $\mathcal O$. $\square$

*Consequences.* Let $P \mid q$ be a prime of $\mathcal O$ (unramified) and $\Pi$ the unique prime of
$\mathcal O[\zeta_{q^2}]$ above it ($P$ is totally ramified there). $\tau_j$ fixes $\Pi$ and acts trivially on the
residue field. Hence (i) $v_\Pi(X(\zeta_{q^2}^j))$ is constant on primitive $j$, with no input used; (ii) the
$(\zeta_{q^2}-1)$-adic digits of $X(\zeta_{q^2}^j)$ are obtained from those of $X(\zeta_{q^2})$ by the automorphism
$y \mapsto (1+y)^j - 1$ (modulo $q$ this is $(1+y)^{j_0}(1+y^q)^{j_1} - 1$ by Lucas, $j = j_0 + qj_1$), so every
"digit polynomial in $j$" is determined by $X(\zeta_{q^2})$ alone; (iii) comparisons between the levels $T \mapsto 1$,
$\zeta_q$, $\zeta_{q^2}$ are the algebra of the injection $R[C_{q^2}] \to R \times R[\zeta_q] \times R[\zeta_{q^2}]$,
$R = \mathcal O_P$. So every digit statement is a consequence of "$X \in R[C_{q^2}]$ and $X\tilde X = n u$" in a local
ring.

**What it rules out.** In Lemma A of the paper the twist $T \mapsto T^j$ is *not* Galois, because the coefficients
contain $\zeta_p$ with $p$ ramified; that is the source of its power (the digits are genuinely polynomials in $j$ of
bounded degree). For $q \nmid h$ this source is absent: any extension of Lemma A to $\nu_q = 2$ by digit comparison
can only use local information, which is known to admit locally consistent non-flat ("Gauss-type") columns. Control:
`scripts/dig_qh_control.py` checks the identity on 250 twists of random $\mu_4$-valued $X$ on $C_9$ (0 failures) and
shows that for $\mu_3$-valued $X$ ($q \mid h$) the twist is in general not induced by Galois (50/50).

## 3. Positivity, row statistics and relabelling

These concern the positive-definite criterion of Czifra, Matolcsi and Szöllősi (arXiv:2511.11230, Theorem 1), which
certifies nonexistence of $\mathrm{BH}(n,h)$ through a positive-definite function built from row-quotient statistics, and
our attempt to lift it to group-invariant matrices.

**Theorem D2 (relabelling).** Let $\beta : C_{q^2} \to C_q \times C_q$, $\beta(i + qj) = (i, j)$ for
$0 \le i, j < q$ (a bijection, not a homomorphism), extended by the identity on $H$. Let $a'$ be any $\mathrm{BH}$ on
$C_q \times C_q \times H$, i.e. a perfect $a' : C_q \times C_q \times H \to \mu_h$, and define the matrix
$M_{s,y} = a'(\beta(y) + \beta(s))$, $s, y \in G = C_{q^2} \times H$. Then:
1. $M$ is a $\mathrm{BH}(|G|, h)$ with unimodular entries;
2. for any rows $s \ne t$ and any coset $c + \langle s - t\rangle$ of the cyclic subgroup of $G$ generated by $s - t$,
   $\prod_{y \in c + \langle s-t\rangle} M_{s,y}\overline{M_{t,y}} = 1$ (the "product-1 partition" property that every
   $G$-invariant matrix has);
3. the projections of the rows to $G/K$ and to $G/C_{q^2}$ are group-invariant.

In general $M$ is not $G$-invariant.

*Proof.* (1) $\sum_y M_{s,y}\overline{M_{t,y}} = \sum_v a'(v + \beta s)\overline{a'(v + \beta t)}$, which vanishes for
$\beta s \ne \beta t$ by perfectness of $a'$. (2) Write $s - t = (w_Q, w_H)$. Since $q \nmid |H|$, by CRT the coset is a
product $(c_Q + \langle w_Q \rangle) \times (c_H + \langle w_H\rangle)$. If $w_Q$ is a unit, the inner product over
$c_Q + \langle w_Q\rangle = C_{q^2}$ is $\prod_v a'(v, y_H + s_H)/\prod_v a'(v, y_H + t_H)$, and the outer product over
$y_H \in c_H + \langle w_H\rangle$ telescopes because $s_H - t_H = w_H$. If $0 \ne w_Q \in qC_{q^2}$, then $s_Q \equiv t_Q
\pmod q$, so $\beta s_Q$ and $\beta t_Q$ have the same first coordinate; $\beta(c_Q + qC_{q^2})$ is a line
$\{x\} \times C_q$, the inner products are products of $a'$ along the same line, and the outer product telescopes again.
If $w_Q = 0$ the inner product has one factor and the outer product telescopes. (3) $y$ and $y + qk$ have the same first
$\beta$-coordinate, so the $G/K$-projection of row $s$ at $c$ is $\sum_j a'(c + \beta(s)_1, j, \cdot)$, which depends only on
$c + s \bmod q$; similarly for $G/C_{q^2}$. $\square$

Check: `scripts/d2check.py` applies this to Do Duc's $\mathrm{BH}(C_5 \times C_5, 6)$, relabelled to $C_{25}$ (where no
$\mathrm{BH}(\mathbb{Z}_{25},6)$ exists): properties 1–3 hold, $M$ is not $C_{25}$-invariant, and row 0 has maximal
off-peak autocorrelation $6$ as a sequence on $C_{25}$.

**What it rules out.** Whenever $\mathrm{BH}(C_q \times C_q \times H, h)$ exists, no nonexistence certificate for
$\mathrm{BH}(C_{q^2} \times H, h)$ can be built only from pairwise row statistics with positivity (for any character and
any averaging over column permutations), quotient projections, coset products and unimodularity. The input such a
certificate must use is $G$-invariance itself, $M_{s+c,y+c} = M_{s,y}$, which the relabelled matrix violates.

**Theorem D1 (proof sketch).** The CMS criterion depends on a $\mathrm{BH}(n,h)$ only through $S_n$-invariant row-quotient
statistics, so it cannot exclude any $(n,h)$ for which some $\mathrm{BH}(n,h)$ exists. Our group-invariant lift replaces
these statistics by distributions on row-quotient multisets, one for each class of differences $d \in G$, and adds the
constraint that every multiset in the support be partitionable into blocks of size $\operatorname{ord}_G(d)$ with product
$1$. Any $\mathrm{BH}(n,h)$ with rows indexed by $G$ whose row-quotient multisets have this partition property gives a
feasible point. Consequently the lift is feasible (i) whenever $4 \mid n$ and $h$ is even and a real Hadamard matrix of
order $n$ exists (its quotient multisets contain $n/2$ entries $-1$, an even number, which can always be distributed
into blocks of size $\ge 2$ with an even number of $-1$ in each), and (ii) for $G = C_{q^2} \times H$ whenever
$\mathrm{BH}(C_q \times C_q \times H, h)$ exists, by Theorem D2. This is a sketch: the exact LP formulation we used is not
part of this release, and the statement should be read as a description of what any such multiset-level lift can see.

## 4. Cohomology does not see the extension class

**Proposition R1 (Shapiro).** For $a : G \to \mu_h$ put $M_s(x) = a(x+s)\overline{a(x)}$, an element of the $G$-module
$A = \mathrm{Fun}(G, \mu_h)$ with $G$ acting by translation, $(t\cdot F)(x) = F(x+t)$. Then
$M_{s+t} = M_s \cdot (s\cdot M_t)$, so $s \mapsto M_s$ is a 1-cocycle. Since $A = \mathrm{CoInd}_1^G \mu_h$, Shapiro's
lemma gives $H^1(G, A) = H^1(1, \mu_h) = 0$; every such cocycle is a coboundary $M_s = (s\cdot b)/b$ with $b$ unique up
to $\mu_h$, and indeed $b = a$. The same holds after restriction to any subgroup, e.g. $K$: $A$ is coinduced, hence
$H^i(K, A) = 0$ for $i \ge 1$. Moreover $H^i(C_q, \mu_h) = 0$ for $i \ge 1$ when $q \nmid h$ ($\mu_h$ is uniquely
$q$-divisible and the cohomology is killed by $q$).

*Proof.* The cocycle identity is $a(x+s+t)\overline{a(x)} = [a(x+s+t)\overline{a(x+s)}]\,[a(x+s)\overline{a(x)}]$; the
rest is Shapiro's lemma and the standard fact that $H^i(C_q, -)$, $i \ge 1$, is annihilated by $q$. $\square$

**What it rules out.** The non-split extension $0 \to C_q \to C_{q^2} \to C_q \to 0$ is the only structural difference
between $C_{q^2}$ and $C_q \times C_q$, and its class $\varepsilon \in H^2(C_q, C_q)$ pairs trivially with every
coefficient module of order prime to $q$. So no cochain-level invariant of the difference cocycle of a $\mu_h$-valued
$a$ (twisted group algebras, Heisenberg- or Weil-type lifts) can distinguish $C_{q^2}$ from $C_q \times C_q$ when
$q \nmid h$. The class $\varepsilon$ is visible only through characters of order $q^2$, with values in
$\mathbb{Q}(\zeta_{q^2 L})$, i.e. through the Galois, ideal and archimedean layers covered by items 1 and 2.

## 5. Multipliers

**Conjugacy.** With $\beta$ as in Theorem D2,

$$\beta \circ (x \mapsto (1+q)x) = \mathrm{sh} \circ \beta,\qquad \mathrm{sh}(i,j) = (i, i+j) \in \mathrm{GL}_2(\mathbb F_q).$$

*Proof.* $(1+q)(i + qj) = i + q(i + j) \bmod q^2$. $\square$

So the multiplier $x \mapsto (1+q)x$, the obvious candidate for a symmetry specific to $C_{q^2}$, is transported by
$\beta$ to a linear automorphism of $C_q \times C_q$, and translations by $K$ are transported to translations. Any
constraint using only this multiplier and $K$-translations transfers verbatim to $C_q \times C_q$, where Do Duc's
objects exist. `scripts/e0_beta.py` lists all affine maps $x \mapsto tx + s$ of $C_{q^2}$ that are $\beta$-conjugate to
affine maps of $\mathbb F_q^2$ ($q = 2,3,5,7$): for $q = 2, 3$ every multiplier is, with a suitable shift; for $q \ge 5$
the units $t \not\equiv \pm 1 \pmod q$ are not. Translations by units of $C_{q^2}$ are never $\beta$-affine; they encode
perfectness itself.

**Lemma F.** There is no perfect $a : C_{q^2} \times H \to \mu_h$ ($q \nmid h$, $q \nmid |H|$) satisfying
$a((1+q)y + s_Q,\ w + s_H) = c\cdot a(y,w)$ for all $(y,w)$, for any constants $s_Q \in C_{q^2}$, $s_H \in H$,
$c \in \mathbb C^\times$.

*Proof.* Let $\gamma(y,w) = ((1+q)y + s_Q, w + s_H)$. For $q$ odd, $\gamma^q$ is the translation by
$t = (qs_Q, qs_H)$, because $(1+q)^q \equiv 1$ and $\sum_{k<q}(1+q)^k \equiv q \pmod{q^2}$. Then
$a(x + t) = c^q a(x)$, and perfectness forces $t = 0$ (otherwise the autocorrelation at $t$ is $c^q|G| \ne 0$). So
$s_Q \in qC_{q^2}$, $s_H = 0$, and $c \in \mu_h$ with $c^q = 1$, so $c = 1$. Write $s_Q = qs'$. On the coset
$y_0 + K$ the map $y \mapsto (1+q)y + qs'$ is the translation by $q(y_0 + s')$, which generates $K$ unless
$y_0 \equiv -s' \pmod q$. So for each $w$, $a(\cdot, w)$ is constant on $q-1$ of the $q$ cosets of $K$. For $\chi$
whose restriction to $C_{q^2}$ has order $q^2$, the sum over a coset of $K$ on which $a$ is constant vanishes, so
$\chi(D)$ is a sum over the single set $S = (-s' + K) \times H$ of size $qm$. Parseval for the function $a\cdot 1_S$ gives
$\sum_{\chi \in \widehat G}|\chi(a 1_S)|^2 = |G|\,|S| = q^3m^2$, while the $(q^2 - q)m$ characters of this kind contribute
$(q^2-q)m\cdot q^2 m = (q-1)q^3m^2$. This is impossible for $q \ge 3$.

For $q = 2$: $\gamma^2(y,w) = (y, w + 2s_H)$, so as before $s_H = 0$ and $c = 1$, and $a(\cdot, w)$ is invariant under
the permutation $y \mapsto 3y + s_Q$ of $C_4$. For $s_Q = 1$ this permutation is $(0\,1)(2\,3)$, for $s_Q = 3$ it is
$(0\,3)(1\,2)$; each transposition joins an even and an odd element, so $\chi(D) = 0$ for every $\chi$ whose
restriction to $C_4$ has order $2$, a contradiction. For $s_Q = 0$ it is $(1\,3)$ and for $s_Q = 2$ it is $(0\,2)$; so
$C_1 = C_3$ or $C_0 = C_2$ in the notation of Theorem Q2, i.e. $b = 0$ or $a = 0$ there, which is impossible for $h$ odd
by Step 4 of Theorem Q2 (that step uses only (1) and $-1 \notin \mu_h$, so it holds for any $H$ of odd order). $\square$

**What it rules out.** A multiplier theorem of the form "every perfect $a$ on $C_{q^2} \times H$ is fixed, up to a scalar
and a translation, by $y \mapsto (1+q)y$" would, by Lemma F, prove Conjecture S2; conversely S2 makes such a statement
vacuously true. So on $C_{q^2} \times H$ a multiplier theorem for $1+q$ is *equivalent* to S2, and the multiplier route
reduces to the original problem. Classical multiplier theorems need a prime $p \mid n$ with $(p, v) = 1$, which is not
available here ($n = v = |G|$).

## The open problem and the remaining entries

The problem left open is **Conjecture S2** (stated at the top), with $a = 2$ as the main case. Items 1–5 show that it
needs an input that sees, at the same time, unimodularity of the coefficients and $G$-invariance (translation
consistency), and that uses the cyclicity of the Sylow subgroup beyond the multiplier $1+q$; ideal-level, local digit,
positivity, cohomological and multiplier arguments each miss one of these.

In terms of Do Duc's list ($n, h \le 100$): before the [Q2 series](../q2-series/README.md), 81 entries with a cyclic Sylow
$q$-subgroup of order $q^2$, $q \nmid h$, were not excluded by any criterion we implemented. The Q2 series closes 17 of
them (and makes $(28,7)$ unconditional), leaving **64**, listed in
[`../remaining-open-cases.json`](../remaining-open-cases.json): 43 with $q = 3$ only, 9 with $q = 2$ only, 7 with
$q = 5$ only, and 5 with two such primes ($q \in \{2,3\}$: 2; $q \in \{2,5\}$: 3). "Open" is relative to our criteria and
our literature search, both of which are incomplete.

The 64 pairs $(n,h)$ (the JSON file also records the primes $q$ for each):

```json
[
  [36, 21], [36, 45], [36, 52], [36, 56], [36, 63], [36, 65], [36, 70], [36, 77], [45, 35], [45, 40],
  [45, 70], [45, 80], [45, 100], [60, 15], [60, 45], [60, 75], [63, 35], [63, 56], [63, 70], [72, 8],
  [72, 16], [72, 20], [72, 26], [72, 32], [72, 35], [72, 40], [72, 44], [72, 52], [72, 56], [72, 64],
  [72, 65], [72, 68], [72, 70], [72, 77], [72, 80], [72, 88], [72, 91], [72, 92], [72, 95], [72, 100],
  [84, 63], [90, 20], [90, 40], [90, 70], [90, 80], [90, 100], [99, 11], [99, 22], [99, 44], [99, 55],
  [99, 77], [99, 88], [100, 48], [100, 55], [100, 62], [100, 66], [100, 72], [100, 75], [100, 77], [100, 84],
  [100, 88], [100, 93], [100, 96], [100, 99]
]
```

## Scripts

Run from `results/obstructions/scripts/`.

| Script | Item | Command | Result | Time |
| --- | --- | --- | --- | --- |
| `fakes.gp` | 1 | `gp -q fakes.gp` | all six: $DD^* = \lvert G\rvert$ exactly; $q \nmid \chi(D)$ for 48/48, 30/30, 66/66, 80/80, 60/60, 42/42 order-$q^2$ characters | 6 s |
| `dig_qh_control.py` | 2 | `sage -python dig_qh_control.py` | 50/50 non-Galois twists for $q \mid h$; 0/250 failures of Proposition D1 for $q \nmid h$ | 2 s |
| `d2check.py` | 3 | `python3 d2check.py` | properties 1–3 hold; not $G$-invariant; row 0 not perfect on $C_{25}$ | < 1 s |
| `e0_beta.py` | 5 | `python3 e0_beta.py` | $x \mapsto (1+q)x$ corresponds to the shear for $q = 2,3,5,7$; lists of $\beta$-affine maps | < 1 s |
