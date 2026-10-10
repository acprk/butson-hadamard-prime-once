# Theorem Q2: no $\mathrm{BH}(\mathbb{Z}_{4q},h)$ for $h$ odd and $q^2 \nmid h$

**Status: independently verified.** The proof below was derived once and then re-derived step by step in a separate,
adversarial check, which also supplied the complete proof of Lemma K. Two typographical slips found in that check are
corrected here (marked *[corrected]*). No peer review. Paper proof only; not formalized in Lean, except that Step 1 is
an instance of the Lean-verified `lemmaA` of this repository.

## Statement

**Theorem Q2.** Let $q$ be an odd prime and $h$ an odd integer with $q^2 \nmid h$. Then there is no perfect sequence
of length $4q$ over $\mu_h$; equivalently, there is no $\mathrm{BH}(C_4 \times C_q, h)$.

If $q \nmid h$ this is Theorem S of the paper ($q \parallel 4q$ and $q$ is unramified in $\mathbb{Q}(\zeta_h)$).
The proof below treats $q \parallel h$. Theorem Q2′ ([theorem-q2-prime.md](theorem-q2-prime.md)) removes the
hypothesis $q^2 \nmid h$.

## Notation

$G = C_4 \times H$ with $H = C_q = \mathbb{Z}/q$ and $C_4 = \langle T\rangle$. Write
$D = \sum_{y \in \mathbb{Z}/4} T^y C_y$ with $C_y \in \mathbb{Z}[\zeta_h][H]$ whose $q$ coefficients lie in $\mu_h$,
and $DD^* = 4q$. For $w \in H$ the *column* $w$ is $(C_0(w), C_1(w), C_2(w), C_3(w))$. Put

$$a = C_0 - C_2,\quad b = C_1 - C_3,\quad s_0 = C_0 + C_2,\quad s_1 = C_1 + C_3,\quad e_\pm = s_0 \pm s_1,\quad f = a + ib .$$

These are the images of $D$ under $T \mapsto 1, -1, i$: $D(T{=}\pm1) = e_\pm$ and $D(T{=}i) = f$. Hence
$e_+e_+^* = e_-e_-^* = ff^* = 4q$ in $\mathbb{Z}[\zeta_{4h}][H]$, and also $\bar f \bar f^* = 4q$ for
$\bar f = a - ib = D(T{=}-i)$. Adding the last two gives

$$aa^* + bb^* = 4q. \tag{1}$$

Let $z = \zeta_h$, $k = \mathbb{Q}(\zeta_h)$, $K = k(i) = \mathbb{Q}(\zeta_{4h})$, and let $\tau \in \mathrm{Gal}(K/k)$ be
the element with $\tau(i) = -i$ (it exists because $h$ is odd, so $i \notin k$).

## Proof (case $q \parallel h$)

**Step 1 (Lemma A at $q$).** Write $4h = qd$ with $q \nmid d$. Then $f, f^* \in \mathbb{Z}[\zeta_{qd}][C_q]$ and
$ff^* = 4q$ with $v_q(4q) = 1$. Lemma A of the paper (Lean: `lemmaA`, with $p = q$ and $n = 4q$) gives, at every prime
$\mathfrak Q \mid q$ of $\mathcal O_K$: all $f(\chi)$, $\chi \in \widehat H$, have the same $\mathfrak Q$-valuation and
$f(\chi) \equiv f(1) \bmod \mathfrak Q^{\alpha+1}$. Since $|f(\chi)|^2 = 4q \ne 0$, the ratio
$r_\chi := f(\chi)/f(1)$ is a $\mathfrak Q$-unit with $r_\chi \equiv 1 \pmod{\mathfrak Q}$, for every $\mathfrak Q \mid q$.

**Step 2 ($\tau$-descent).** Fix $\chi$ and put $r = r_\chi \in K$. Since $K$ is abelian, complex conjugation commutes
with every embedding, so $|r| = 1$ at every embedding. Valuations of $r$:
- at primes not above $2q$: $f(\chi)$ and $f(1)$ divide $4q$, so they are units;
- at primes above $q$: $r$ is a unit by Step 1;
- at primes above $2$: $2$ is unramified in $k$ ($h$ odd) and ramified in $K = k(i)$, so each prime of $k$ above $2$
  has exactly one prime of $K$ above it, which is therefore $\tau$-fixed; hence $v_P(\tau r) = v_P(r)$.

So $\varepsilon := \tau(r)/r$ is a unit at every prime with $|\varepsilon| = 1$ at every embedding; by Kronecker's
theorem it is a root of unity. Step 1 at $\tau^{-1}(\mathfrak Q)$ gives $\tau(r) \equiv 1 \pmod{\mathfrak Q}$, so
$\varepsilon \equiv 1 \pmod{\mathfrak Q}$. For a root of unity of order $m > 1$, $1 - \varepsilon$ is a unit if $m$ is
not a prime power and divides $p$ if $m$ is a power of the prime $p$; so $\varepsilon$ has $q$-power order. Thus $\varepsilon \in \mu_{q^\infty}(K) = \mu_q \subset k$, so $\tau(\varepsilon) = \varepsilon$. But also
$\tau(\varepsilon) = r/\tau(r) = \varepsilon^{-1}$. Hence $\varepsilon^2 = 1$, and since $\varepsilon$ has odd order,
$\varepsilon = 1$. So $r_\chi \in k$ for every $\chi$.

**Step 3 (proportionality).** $K = k \oplus ik$, and $a(\chi), b(\chi) \in k$ because the coefficients of $a, b$ lie in
$\mathbb{Z}[\zeta_h]$ and $\chi$ takes values in $\mu_q \subset k$. Comparing $k$- and $ik$-parts of
$f(\chi) = r_\chi f(1)$ gives $a(\chi) = r_\chi a(1)$ and $b(\chi) = r_\chi b(1)$. Hence
$b(1)\,a(\chi) = a(1)\,b(\chi)$ for all $\chi$, and by Fourier inversion $b(1)\,a = a(1)\,b$ in $k[H]$. Either
$b(1) = 0$, and then $b(\chi) = 0$ for all $\chi$, so $b = 0$; or $a = \kappa b$ with $\kappa = a(1)/b(1) \in k$.

**Step 4 ($b \ne 0$, $a \ne 0$).** If $b = 0$, then (1) gives $aa^* = 4q$. Its identity coefficient is
$\sum_{w} |C_0(w) - C_2(w)|^2 = 4q$ *[corrected: this is the identity coefficient of (1), i.e. of the $T^0$
equation, not of the $T^2$ equation]*. Each term is at most $4$, with equality only if $C_2(w) = -C_0(w)$, which is
impossible because $-1 \notin \mu_h$. So the sum is $< 4q$, a contradiction. The case $a = 0$ is symmetric. Hence
$\kappa \ne 0$, $b \ne 0$ and $f = (\kappa + i)\,b$.

**Step 5 ($\kappa$ totally real).** $ff^* = (\kappa+i)(\bar\kappa - i)\,bb^*$. At any $\chi$,
$(bb^*)(\chi) \in k^\times$, so $(\kappa+i)(\bar\kappa-i) = |\kappa|^2 + 1 + i(\bar\kappa - \kappa) \in k$. As
$\bar\kappa - \kappa \in k$, this forces $\bar\kappa = \kappa$; $k$ is abelian, so $\kappa$ is totally real. Then
$bb^* = \beta := 4q/(1+\kappa^2)$ is a scalar.

**Step 6 (column law).** Write the column $w$ as $(z^{x_0}, z^{x_1}, z^{x_2}, z^{x_3})$ and let
$S = \operatorname{supp} b = \operatorname{supp} a$, $s = |S|$. For $w \in S$, $z^{x_0} - z^{x_2} = \kappa\,(z^{x_1} - z^{x_3})$.
Apply complex conjugation and use $\overline{z^x - z^y} = -(z^x - z^y)\,z^{-x-y}$ and $\bar\kappa = \kappa$; dividing by the
original equation gives $x_0 + x_2 \equiv x_1 + x_3 \pmod h$. Since $h$ is odd we may halve exponents: with
$d = (x_0-x_2)/2$, $d' = (x_1-x_3)/2$ and $\varphi_w = z^{(x_0+x_2)/2}$,

$$\text{column } w = \varphi_w\,(z^{d}, z^{d'}, z^{-d}, z^{-d'}),\qquad \kappa = \kappa(d,d') := \frac{z^{d}-z^{-d}}{z^{d'}-z^{-d'}}\quad (w \in S),$$

with $d, d' \ne 0$, and $\kappa$ is the same for all $w \in S$. Off $S$ the columns are $(u_w, v_w, u_w, v_w)$. Since
$|z^d - z^{-d}|^2 = 2 - z^{2d} - z^{-2d}$, the identity coefficient of (1) reads

$$\sum_{w \in S} (4 - \Sigma_4(w)) = 4q,\qquad \Sigma_4(w) := z^{2d}+z^{-2d}+z^{2d'}+z^{-2d'} . \tag{2}$$

### Lemma K (sine-ratio rigidity)

**Lemma K.** Let $h$ be odd and $d_1, d_1', d_2, d_2' \in \mathbb{Z}/h$ nonzero. If $\kappa(d_1,d_1') = \kappa(d_2,d_2')$ and
this common value is not $\pm 1$, then $(d_2, d_2') = \pm(d_1, d_1')$.

*Proof.* Put $(A,B) = (d_1,d_1')$, $(C,D) = (d_2,d_2')$. Clearing denominators, the equality is
$(z^A - z^{-A})(z^D - z^{-D}) = (z^B - z^{-B})(z^C - z^{-C})$, that is

$$\sum_{p \in P} z^p - \sum_{n \in N} z^n = 0,\qquad P = \{\pm(A+D), \pm(B-C)\},\quad N = \{\pm(B+C), \pm(A-D)\}$$

(multisets). Read this as a vanishing sum of $8$ elements of $\mu_{2h} = \mu_h \sqcup (-\mu_h)$: four "positive" terms in
$\mu_h$ and four "negative" terms in $-\mu_h$. Two elements of $\mu_{2h}$ lie in the same class iff their ratio has odd
order.

Cancel the multiset intersection $P \cap N$, of size $k$, and let $P' = P \setminus N$, $N' = N \setminus P$. Since $P$ and
$N$ are closed under negation of exponents, so is $P \cap N$. If $k$ were odd, $P'$ and $N'$ would be negation-closed of
odd size, hence both would contain the exponent $0$ (the only self-inverse element, $h$ being odd), contradicting
$P' \cap N' = \emptyset$. So $k \in \{0, 2, 4\}$.

Every vanishing sum of roots of unity is a disjoint union of minimal vanishing sub-sums. By Poonen–Rubinstein
(Theorem 3 of *The number of intersection points made by the diagonals of a regular polygon*, SIAM J. Discrete Math.
1998), the minimal vanishing sums of weight $\le 8$ are, up to rotation, $R_2, R_3, R_5, (R_5{:}R_3), R_7, (R_5{:}2R_3),
(R_5{:}3R_3), (R_7{:}R_3)$. A rotated $R_p$ ($p$ odd) lies in a single class; $(R_5{:}jR_3)$ consists of $5-j$ elements of
one class and $2j$ of the other; $(R_7{:}R_3)$ has $6$ and $2$. So the possible sign patterns (positive, negative) are
$(3,0)$, $(5,0)$, $(7,0)$, $(4,2)$, $(3,4)$, $(2,6)$, $(6,2)$ and their swaps, plus $(1,1)$ for $R_2$. An $R_2$ piece
$\{x, -x\}$ in the remaining sum would be a common element of $P'$ and $N'$, which was excluded. For $k = 2$ we need total
pattern $(2,2)$ of weight $4$, and for $k = 0$ pattern $(4,4)$ of weight $8$; neither is a sum of the patterns above
(weight $4$ admits no piece combination at all; weight $8$ splits only as $8$ or $3+5$, giving $(6,2)$, $(2,6)$, $(8,0)$,
$(3,5)$, $(5,3)$, $(0,8)$). Hence $k = 4$, that is $P = N$.

Finally compare. $A + D = \pm(A - D)$ forces $D = 0$ or $A = 0$ ($h$ odd), excluded. If $A + D = B + C$, the remaining
pair gives $B - C = \pm(A - D)$; the sign $+$ yields $A = B$, $C = D$, so $\kappa = 1$, and the sign $-$ yields
$(C,D) = (A,B)$. If $A + D = -(B+C)$, then $B - C = A - D$ yields $(C,D) = -(A,B)$, and $B - C = -(A-D)$ yields
$A = -B$, so $\kappa = -1$. $\square$

Check: `scripts/lemmaK_check.py` searches all odd $h \le 2001$ ($\approx 6.7 \times 10^8$ representative pairs; a
coincidence at one embedding is an equality in $k$) and finds no nontrivial coincidence.

### Lemma (rational values of $\Sigma_4$)

**Lemma.** For $h$ odd and $d, d' \ne 0$, if $\Sigma_4 = z^{2d}+z^{-2d}+z^{2d'}+z^{-2d'}$ is rational, then
$\Sigma_4 = -1$ (and $z^{\pm 2d}, z^{\pm 2d'}$ are the four primitive fifth roots of unity) or $\Sigma_4 = -2$ (and $z^{2d},
z^{2d'}$ have order $3$).

*Proof.* $\Sigma_4$ is an algebraic integer, so $\Sigma_4 = n \in \mathbb{Z}$ with $|n| < 4$ ($n = 4$ needs $2d = 0$;
$n = -4$ needs $z^{2d} = -1$). Let $\alpha = z^{2d} \ne 1$, $\beta = z^{2d'} \ne 1$ (both of odd order). If
$n \ge 0$, then $\alpha + \alpha^{-1} + \beta + \beta^{-1} + n\cdot(-1) = 0$ is a vanishing sum with sign pattern
$(4, n)$ in which all $n$ negative terms equal $-1$. No $R_2$ piece occurs, since $\alpha^{\pm1}, \beta^{\pm1} \ne 1$. The
minimal sums in the list above consist of distinct elements, and each mixed piece contains at least two distinct elements
of each class. So the negative terms can lie neither in a single-class piece (three or more distinct elements) nor in a
mixed piece (two distinct negatives); hence $n = 0$. But then $(4,0)$ would be a sum of single-class pieces of odd prime
weights adding up to $4$, which is impossible. If $n = -k < 0$, then
$\alpha+\alpha^{-1}+\beta+\beta^{-1} + k \cdot 1 = 0$ has all $4 + k$ terms in one class, so it is a union of rotated
$R_p$'s, each with distinct elements: $k = 1$ gives one $R_5 = \mu_5$ (it contains $1$); $k = 2$ gives two copies of
$\mu_3$; $k = 3$ would need three copies of $1$ in pieces of total weight $7$, impossible. $\square$

`scripts/sigma4.py` confirms numerically that only $-2$ and $-1$ occur for odd $h \le 201$.

### Conclusion of the proof

By Lemma K, either $\kappa = \pm 1$, or all $(d_w, d'_w)$, $w \in S$, equal $\pm(d, d')$ for one pair, in which case
$\Sigma_4(w)$ does not depend on $w$.

*Case $\kappa = \pm 1$.* Replacing $D$ by $TD$ replaces $\kappa$ by $-1/\kappa$, so assume $\kappa = 1$. Then
$z^d + z^{-d'} - z^{-d} - z^{d'} = 0$ is a vanishing sum of $4$ roots of unity, hence two pairs $\{x, -x\}$; the only
admissible pairing ($d \ne 0$, $-1 \notin \mu_h$) is $d = d'$. So the columns are $(c, c, e, e)$ on $S$ and
$(u, v, u, v)$ off $S$. Then $e_- = 2(u - v)\,1_{S^c}$, and the identity coefficient of $e_-e_-^* = 4q$ gives
$\sum_{w \notin S} |u_w - v_w|^2 = q$. Also $\beta = 2q$, so $\sum_{w \in S} |a_w|^2 = 2q$. Each nonzero term is
$|z^x - z^y|^2 = 2 - (\zeta + \zeta^{-1})$ with $\zeta \ne 1$ of odd order $m$, whose Galois average is
$2 - 2\mu(m)/\varphi(m) \in [7/4, 3]$ (since $2\mu(m)/\varphi(m) \in [-1, 1/4]$ for odd $m > 1$). Averaging the two
rational identities over $\mathrm{Gal}(k/\mathbb{Q})$ gives $2q \le 3s$ and $q \le 3(q - s)$, hence $s = 2q/3$, so
$q = 3$ and $s = 2$, which is excluded below.

*Case $\kappa \ne \pm 1$.* By (2), $s\,(4 - \Sigma_4) = 4q$, so $\Sigma_4 = 4 - 4q/s$ is rational, hence $-1$ or $-2$.
$\Sigma_4 = -2$ gives $3s = 2q$: $q = 3$, $s = 2$. $\Sigma_4 = -1$ gives $5s = 4q$: $q = 5$, $s = 4$.

*$q = 3$, $s = 2$.* $b$ is supported on two points $u \ne v$ of $\mathbb{Z}/3$, so the coefficient of $bb^*$ at $u - v$
is $b_u \overline{b_v} \ne 0$ (as $u - v \ne v - u$). This contradicts $bb^* = \beta$ scalar.

*$q = 5$, $s = 4$, $\Sigma_4 = -1$.* Here $\zeta := z^{d}$ is a primitive fifth root and $z^{d'} = \zeta^{\pm 2}$, the
same for all $w \in S$ up to the sign of $(d,d')$, which does not affect $s_0, s_1$. Let $w_0$ be the point off $S$ and
$\theta = \zeta + \zeta^{-1} - \zeta^{2} - \zeta^{-2}$ ($\theta^2 = 5$). Then

$$e_+ = -\varphi\,1_S + 2(u+v)\,\delta_{w_0},\qquad e_- = \theta\,\varphi\,1_S + 2(u-v)\,\delta_{w_0}$$

*[corrected: the term $2(u-v)\delta_{w_0}$ of $e_-$ was omitted in the original derivation; it does not matter once $u = v$ is
shown]*, with $u = u_{w_0}$, $v = v_{w_0}$. The identity coefficient of $e_+e_+^* = 20$ gives $4 + 4|u+v|^2 = 20$, so
$|u + v| = 2$ and $u = v$. Put $A = \varphi\,1_S$. Then $e_- = \theta A$ gives $AA^* = 4$, and
$e_+ = -A + 4u\,\delta_{w_0}$ gives $e_+e_+^* = 20 - 4(\bar u\,A\,\delta_{-w_0} + u\,\delta_{w_0}A^*)$. Hence
$\bar u\,\varphi_{w_0+t} + u\,\overline{\varphi_{w_0-t}} = 0$ for every $t \ne 0$, i.e.
$u^2 = -\varphi_{w_0+t}\varphi_{w_0-t}$, so $-1 \in \mu_h$, a contradiction. $\square$

## Nature of the result

Steps 1–3 are Lemma A followed by a standard Galois descent; the descent is the special case of a cross-ratio descent in
which only one odd prime occurs, so that the two-term ratio $f(\chi)/f(1)$ already descends. The post-descent arithmetic
(Steps 4–6, Lemma K, the rational values of $\Sigma_4$, the endgame) is new but elementary. We regard Q2 as a short
corollary-level result, not as a new method.

## Entries of Do Duc's open list closed

Among the pairs $(n,h)$, $n,h \le 100$, listed as open by Do Duc (2019, Remark 3.13) and not excluded by any criterion we
implemented (see [README.md](README.md)), Theorem Q2 closes

$(20,45)$, $(28,21)$, $(28,63)$, $(52,39)$, $(68,51)$, $(92,23)$, $(92,69)$,

and in addition $(28,7)$, which our earlier pipeline had excluded only by a GRH-conditional column computation.
It also covers $(28,35)$, $(28,77)$, $(28,91)$ directly; these had been excluded only conditionally on $(28,7)$.

## Checks and reproduction

All commands are run from `results/q2-series/scripts/`.

| Check | Command | Result | Time |
| --- | --- | --- | --- |
| Lemma K, odd $h \le 201$ / $203 \le h \le 2001$ | `python3 lemmaK_check.py 3 201` / `python3 lemmaK_check.py 203 2001` | 0 nontrivial coincidences | 0.4 s / 4 min |
| rational $\Sigma_4$, odd $h \le 201$ | `python3 sigma4.py` | values $\{-2, -1\}$ only | 5 s |
| exhaustive search, all perfect sequences of length $4q$ | `cc -O2 -o bhcol bhcol.c -lm && ./bhcol 3 15` (also `3 21`, `3 33`, `3 39`, `5 5`) | 0 sequences | 0.1–23 s |
| controls for `bhcol` | `./bhcol 3 6`, `./bhcol 3 12`, `./bhcol 3 18` | 432, 864, 1296 | < 1 s |
| structured search using only Steps 1–3, 5 | `python3 structured.py 5 15` (also `7 21`) | $(20,15)$: 4 survivors, 4800 completions, 0 perfect; $(28,21)$: 0 survivors | 17 s, 1 s |
| control for `structured.py` | `python3 structured.py 3 6 withzero` | 216 hits ($=$ the $a = 0$ objects of $\mathrm{BH}(\mathbb{Z}_{12},6)$) | 1 s |

`bhcol.c` makes no use of the theory: it enumerates column 0 up to Galois, rotation and reversal, solves the last column,
and re-verifies every hit by direct autocorrelation at all embeddings. `structured.py` assumes only Steps 1–3 and 5
($a = \kappa b$ with $\kappa$ real and nonzero) and computes the $\kappa$-classes from all $h^4$ column types; it confirms the
column law and the class sizes $2h$ and $h(h-1)$ predicted by Lemma K. Python scripts need `numpy`; `lemmaK_check.py`
also needs `mpmath`.
