# Theorem E1: no $\mathrm{BH}(\mathbb{Z}_{4q^2},h)$ for $h$ odd under condition (W)

**Status: single derivation plus exhaustive checks; not independently re-verified.** No peer review. Paper proof only.

**Nature.** Step 1 is B. Schmidt's field descent (Schmidt 1999; Leung–Schmidt 2005), used here with $q \mid h$ allowed.
Steps 2–3 follow the single-coset concentration and Parseval template of K. H. Leung and B. Schmidt, *Finiteness of
circulant weighing matrices of fixed weight* (J. Combin. Theory Ser. A, 2011). What is new is the endgame (Steps 2–5):
the $C_4$ integrality argument, the deficiency bookkeeping, and two short arguments that use $h$ odd. Someone fluent in
that template could plausibly write this proof in an afternoon; we regard E1 as a corollary-level result. It is recorded
because the descent of Theorem Q2 genuinely fails at $n = 4q^2$ (see the last section).

## Statement

**Theorem E1.** Let $q$ be an odd prime and $h$ an odd integer with $q^2 \nmid h$, and assume

$$\text{(W)}\qquad \operatorname{ord}_{\operatorname{lcm}(h,q^2)}(2) \ne \operatorname{ord}_{\operatorname{lcm}(h,q)}(2).$$

Then there is no perfect sequence of length $4q^2$ over $\mu_h$, i.e. no $\mathrm{BH}(C_4 \times C_{q^2}, h)$.
Both $q \parallel h$ and $q \nmid h$ are allowed.

## Notation

$G = C_4 \times C_{q^2}$, $C_4 = \langle T \rangle$, $C_{q^2} = \langle g \rangle$,
$D = \sum_{y \in \mathbb{Z}/4,\, w \in \mathbb{Z}/q^2} C_y(w)\, T^y g^w$ with $C_y(w) \in \mu_h$ and $DD^* = 4q^2$. Let $\psi$
be the character of $C_4$ with $\psi(T) = i$. Let $Q_0 = q\mathbb{Z}/q^2\mathbb{Z}$ (order $q$). The *classes* are the
cosets $\rho + Q_0$, $\rho \in \{0,\dots,q-1\}$, and the *fibres* are $t \mapsto C_y(\rho + qt)$, $t \in \mathbb{Z}/q$. Put

$$A_{y,\rho}(s) = \sum_{t} C_y(\rho + qt)\,\zeta_q^{st},\qquad B_{j,\rho}(s) = \sum_y i^{jy} A_{y,\rho}(s),$$

so $B_{j,\rho}(s)$ is the two-dimensional Fourier transform of the $4 \times q$ block of class $\rho$. Let
$D'$ be the image of $D$ in $\mathbb{Z}[\zeta_h][C_4 \times C_{q^2}/Q_0]$, so $D'_{y,\rho} = A_{y,\rho}(0)$ and
$D'D'^* = 4q^2$. Let $K' = \mathbb{Q}(\zeta_{4h}, \zeta_q)$ and $L = K'(\zeta_{q^2}) = \mathbb{Q}(\zeta_{4\operatorname{lcm}(h,q^2)})$;
since $q^2 \nmid h$, $[L : K'] = q$. For a character $\chi$ of order $q^2$, $\chi(g) = \zeta_{q^2}^u$, put $s = u \bmod q$. Then

$$D(\psi^j \times \chi) = \sum_{\rho} \zeta_{q^2}^{u\rho}\, B_{j,\rho}(s),\qquad B_{j,\rho}(s) \in K'. \tag{$*$}$$

## Proof

**Step 1 (descent; concentration).** Let $x = D(\psi^j \times \chi)$ and $\sigma \in \mathrm{Gal}(L/K')$. Since $D$ has
coefficients in $\mathbb{Q}(\zeta_h) \subset K'$ and $\psi$ takes values in $\mathbb{Q}(i) \subset K'$,
$\sigma(x) = D(\psi^j \times \chi^{u'})$ for some $u'$. Put $r_\sigma = \sigma(x)/x$.
- Primes above $q$: $L/K'$ is totally ramified above $q$ ($e_q(K') = q - 1$, $e_q(L) = q(q-1)$), so $\sigma$ fixes every
  prime above $q$ and $v_P(\sigma x) = v_P(x)$.
- Primes above $2$: in $\mathrm{Gal}(L/\mathbb{Q}) = (\mathbb{Z}/4)^* \times (\mathbb{Z}/\operatorname{lcm}(h,q^2))^*$ the
  decomposition group of $2$ is $(\mathbb{Z}/4)^* \times \langle 2 \rangle$. The group $\mathrm{Gal}(L/K')$ is the subgroup of
  order $q$ of elements $\equiv 1 \bmod 4\operatorname{lcm}(h,q)$. It lies in $\langle 2\rangle$ iff
  $2^{\operatorname{ord}_{\operatorname{lcm}(h,q)}(2)} \not\equiv 1 \bmod \operatorname{lcm}(h,q^2)$, which is (W). So
  $\sigma$ fixes every prime above $2$.
- Other primes do not divide $x$, because $x\bar x = 4q^2$.

Hence $r_\sigma$ is a unit with $|r_\sigma| = 1$ at every embedding ($L$ is abelian), so $r_\sigma \in \mu_L$ by Kronecker.
The map $\sigma \mapsto r_\sigma$ is a 1-cocycle of $\mathrm{Gal}(L/K') \cong C_q$ with values in
$\mu_L = \mu_{q^2} \times \mu_{M'}$, $q \nmid M'$. On $\mu_{M'} \subset K'$ the action is trivial and
$H^1 = \mathrm{Hom}(C_q, \mu_{M'}) = 0$. On $\mu_{q^2}$ a generator acts by $\zeta \mapsto \zeta^{1+q}$; the image of
$\sigma - 1$ is $\mu_q$ and the norm is $\zeta \mapsto \zeta^{\sum_{k<q}(1+q)^k} = \zeta^{q}$ ($q$ odd), with kernel $\mu_q$;
so $H^1 = 0$. Thus $r_\sigma = \sigma(\eta)/\eta$ with $\eta \in \mu_L$, and $x/\eta \in K'$, i.e. $x \in \mu_{q^2} K'$.

The elements $\zeta_{q^2}^{u\rho}$, $\rho = 0, \dots, q-1$, form a $K'$-basis of $L$ up to factors in $\mu_q \subset K'$
($\rho \mapsto u\rho \bmod q$ is bijective and $\zeta_{q^2}$ has minimal polynomial $X^q - \zeta_q$ over $K'$). By $(*)$,
$x$ has exactly one nonzero coordinate:

> **Concentration.** For each $(j, s)$ with $s \ne 0$ there is exactly one class $c_j(s)$ with
> $B_{j,c_j(s)}(s) \ne 0$, and $|B_{j,c_j(s)}(s)|^2 = 4q^2$.

**Step 2 ($C_4$ integrality).** Fix $s \ne 0$ and let $J_\rho = \{ j : c_j(s) = \rho \}$. Let $\tau$ fix
$\mathbb{Q}(\zeta_{\operatorname{lcm}(h,q)})$ and send $i \mapsto -i$ ($h$ odd). Since
$A_{y,\rho}(s) \in \mathbb{Q}(\zeta_{\operatorname{lcm}(h,q)})$, $B_{3,\rho}(s) = \tau(B_{1,\rho}(s))$, so $1$ and $3$
always lie in the same $J_\rho$. If $J_\rho = \{0\}$, then by Fourier inversion on $C_4$, $A_{y,\rho}(s) = B_{0,\rho}(s)/4$
for all $y$, so $A_{y,\rho}(s)\overline{A_{y,\rho}(s)} = 4q^2/16 = q^2/4$, which is not an algebraic integer. The same
holds for $J_\rho = \{2\}$. Hence for each $s$ either $c_0 = c_1 = c_2 = c_3$, or $c_0 = c_2 \ne c_1 = c_3$; so
$n_\rho(s) := |J_\rho| \in \{0, 2, 4\}$.

**Step 3 (class Parseval).** Parseval on the $4 \times q$ block of class $\rho$ gives
$\sum_{j,s} |B_{j,\rho}(s)|^2 = 4q \cdot 4q = 16q^2$. By Step 1 the part with $s \ne 0$ equals $4q^2 N_\rho$ with
$N_\rho := \sum_{s \ne 0} n_\rho(s)$, and the part with $s = 0$ equals $4 \sum_y |D'_{y,\rho}|^2$. Hence

$$\sum_y |D'_{y,\rho}|^2 = q^2(4 - N_\rho),\qquad \sum_\rho N_\rho = 4(q-1),\qquad \sum_\rho (4 - N_\rho) = 4,$$

and $N_\rho \in \{0, 2, 4\}$. Only two patterns remain: (I) one class with $N = 0$ and all others with $N = 4$; (II) two
classes with $N = 2$ and all others with $N = 4$. Classes with $N = 4$ have $D'_{\cdot,\rho} = 0$.

**Step 4 (pattern I is impossible).** If $N_{\rho_0} = 0$, then $A_{y,\rho_0}(s) = 0$ for all $s \ne 0$, so every fibre
of $\rho_0$ is constant, $C_y(\rho_0 + qt) = x_y$. Then $D' = q\, X g^{\rho_0}$ with $X = \sum_y x_y T^y$, and
$D'D'^* = 4q^2$ gives $XX^* = 4$, a $\mathrm{BH}(C_4, h)$. Its $T^2$ coefficient
$x_0\bar x_2 + x_2 \bar x_0 + x_1 \bar x_3 + x_3 \bar x_1 = 0$ is a vanishing sum of four roots of unity of odd order,
impossible by Lam–Leung ($4$ is not a sum of odd primes).

**Step 5 (pattern II is impossible).** Let $b \ne c$ be the two classes with $N = 2$ and write
$D' = U_b g^b + U_c g^c$ with $U_\rho \in \mathbb{Z}[\zeta_h][C_4]$. As $q$ is odd, $b - c \ne c - b$, so $D'D'^* = 4q^2$
gives $U_bU_b^* + U_cU_c^* = 4q^2$ and $U_bU_c^* = 0$. Hence for each $j$ exactly one of $U_b(\psi^j)$, $U_c(\psi^j)$ is
nonzero, with absolute value squared $4q^2$. By Step 3, $\sum_y |U_{b,y}|^2 = 2q^2$, so $U_b$ is nonzero at exactly two
characters; this set is closed under $j \mapsto -j$ ($\tau$), so it is $\{0, 2\}$ for one class and $\{1, 3\}$ for the
other, say $c$. Then $U_c(1) = U_c(-1) = 0$, i.e. $D'_{y+2,c} = -D'_{y,c}$.

Since $N_c = 2$, there is exactly one $s_0 \ne 0$ with $n_c(s_0) = 2$, and $A_{y,c}(s) = 0$ for $s \notin \{0, s_0\}$.
So each fibre of $c$ has the form $z_t = \alpha + \beta\,\zeta_q^{-s_0 t}$. The $q \ge 3$ values $z_t$ lie on the unit
circle, which forces $\alpha = 0$ or $\beta = 0$: either the fibre is constant, or it has a single frequency and
$D'_{y,c} = 0$. If $D'_{y,c} \ne 0$, then the fibres $y$ and $y + 2$ are both constant, and $q x_{y+2} = -q x_y$, so
$-1 \in \mu_h$, impossible. Hence $D'_{\cdot,c} = 0$, contradicting $\sum_y |D'_{y,c}|^2 = 2q^2$. $\square$

**Where the hypotheses are used.** (W) only in Step 1. $h$ odd: Step 2 ($\tau$ exists), Step 4 (no
$\mathrm{BH}(C_4,h)$) and Step 5 ($-1 \notin \mu_h$). The control script `e1_endgame_controls.py` takes random
generalized Frank sequences $\mathrm{BH}(\mathbb{Z}_{36},6)$ and $\mathrm{BH}(\mathbb{Z}_{100},10)$ ($h \equiv 2 \bmod 4$):
they pass Steps 1–3 and escape exactly at Steps 4/5 (pattern I with $X$ a $\mathrm{BH}(C_4,h)$; pattern II with
$x_{y+2} = -x_y$).

## Why the proof of Theorem Q2 does not extend

At $n = 36$ the $\tau$-descent of Theorem Q2 is false on existing objects. Take the generalized Frank sequences
$a(6j+k) = \zeta_6^{\pi(k) j}\zeta_6^{\psi(k)}$ ($\pi \in S_6$, $\psi \in (\mathbb{Z}/6)^6$), which are
$\mathrm{BH}(\mathbb{Z}_{36}, 6)$. Here $h = 6 \equiv 2 \bmod 4$, $i \notin \mathbb{Q}(\zeta_6)$ and $2$ is unramified in
$\mathbb{Q}(\zeta_3)$, exactly as in Q2. Q2's Steps 2–3 would force one real $\kappa$; among 4000 random objects only 376
($h = 6$) and 402 ($h = 18$) have this property. For the explicit object $\pi = (1,0,4,5,3,2)$, $\psi = (4,0,2,0,3,3)$ an
exact computation in $\mathbb{Q}(\zeta_{36})$ shows: one prime above $3$ (so $\tau$-fixed), $v(f(\chi)) = 6$ for all nine
characters, and $\varepsilon = \tau(r)/r = -1$ at the order-9 characters $\chi_1, \chi_4, \chi_7$. So what fails is the
residue-1 part of the comparison at order $q^2$, not the valuation part. Any root of unity $\varepsilon$ with
$\tau(\varepsilon) = \varepsilon^{-1}$ lies in $\mu_4$, and these objects realise $\varepsilon = -1$ while satisfying every
other hypothesis of Q2's Steps 1–3.

## Entries of Do Duc's open list closed

$(36,15)$, $(36,75)$, $(100,15)$, $(100,35)$, $(100,45)$, $(100,85)$, $(100,95)$ (all with $q \parallel h$ and (W)).

Not closed: $(36,21)$ and $(100,55)$ ($q \parallel h$, (W) fails: $\operatorname{ord}_{63}2 = \operatorname{ord}_{21}2 = 6$,
$\operatorname{ord}_{275}2 = \operatorname{ord}_{55}2 = 20$); $(36,45)$, $(36,63)$, $(100,75)$ ($q^2 \mid h$, no descent field);
$(36,65)$, $(36,77)$, $(100,77)$, $(100,93)$, $(100,99)$ ($q \nmid h$, (W) fails). If (W) fails, $2$ splits in $L/K'$,
$\sigma$ moves the primes above $2$, and $r_\sigma$ need not be a unit.

## Checks and reproduction

Run from `results/q2-series/scripts/`.

| Check | Command | Result | Time |
| --- | --- | --- | --- |
| brute force of Steps 2–5 for $n = 36$, given only concentration (Step 1): all $h^{12}$ class blocks, all complementary triples, full perfectness test | `cc -O2 -o blockcheck blockcheck.c -lm && ./blockcheck 3`; `./blockcheck 5` | $h=3$: 207 admissible blocks, 0 triples, 0 perfect; $h=5$: 625 admissible, 0 triples, 0 perfect | 0.05 s; 19 s |
| positive control for `blockcheck` | `python3 blockcheck_poscontrol.py ./blockcheck 20` | 20/20 generalized Frank $\mathrm{BH}(\mathbb{Z}_{36},6)$ pass and are found perfect | 1 s |
| endgame controls ($h \equiv 2 \bmod 4$) | `python3 e1_endgame_controls.py` | $q=3,h=6$: patterns I/II = 419/1581; $q=5,h=10$: 93/707 | 1 s |
| failure of Q2's descent at $n = 36$ (numerical) | `python3 q2_failure_n36.py` | one real $\kappa$ in 376/4000 ($h=6$), 402/4000 ($h=18$) | 2 s |
| failure of Q2's descent at $n = 36$ (exact) | `sage q2_failure_n36_exact.sage` | first object: valuations all 6, $\varepsilon$ of order 2 at $\chi_1,\chi_4,\chi_7$ | 2 s |
| which entries satisfy (W) | `python3 closed_entries.py` (see [README.md](README.md)) | the seven entries above | < 1 s |
