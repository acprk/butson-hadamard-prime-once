"""Control for Proposition D1 (twist = Galois when q does not divide h).
For X in O[C_9] and j a unit mod 9, compare X(zeta_9^j) with tau_j(X(zeta_9)), where tau_j fixes the coefficient field.
 (1) q | h (coefficients in Z[zeta_3], ramified at 3): for random mu_3-valued sequences the twist is in general NOT induced
     by Galois, so twisting is a genuine constraint (the Lemma A regime). The Frank sequence of length 9 over mu_3 is printed
     with its P-valuations for reference.
 (2) q = 3 does not divide h = 4: for random mu_4-valued sequences the identity X(zeta^j) = tau_j X(zeta) holds every time,
     as Proposition D1 says, so twisting carries no information.
usage: sage -python dig_qh_control.py
"""
from sage.all import *
M = CyclotomicField(9, 'u'); u = M.gen(); w = u**3
a = [w**((y // 3) * (y % 3)) for y in range(9)]
assert all(sum(a[(x+g) % 9] * a[x].conjugate() for x in range(9)) == (9 if g == 0 else 0) for g in range(9))
P = M.primes_above(3)[0]
vals = [sum(a[y] * u**(j*y) for y in range(9)) for j in range(9)]
print("Frank 9/mu_3: P-valuations of X(zeta9^j), j=0..8 (e=6):", [v.valuation(P) if v != 0 else 'inf' for v in vals])
for j in [2, 4, 5, 7, 8]:
    fix3 = [s for s in range(1, 9) if gcd(s, 9) == 1 and s % 3 == 1]   # automorphisms fixing zeta_3
    ok = any(M.hom([u**s])(vals[1]) == vals[j] for s in fix3)
    print("  j=%d: X(zeta^j) is a conjugate of X(zeta) under Gal(Q(zeta9)/Q(zeta3))? %s" % (j, ok))
# generic (non-perfect) elements: q|h coefficients (Z[zeta_3]) vs q∤h coefficients (Z[zeta_4] inside Q(zeta_36))
set_random_seed(1)
bad = 0
for trial in range(50):
    b = [w**randint(0, 2) for y in range(9)]
    vals = [sum(b[y] * u**(j*y) for y in range(9)) for j in range(9)]
    fix3 = [s for s in range(1, 9) if gcd(s, 9) == 1 and s % 3 == 1]
    if not all(any(M.hom([u**s])(vals[1]) == vals[j] for s in fix3) for j in [2, 4, 5, 7, 8]): bad += 1
print("random mu_3-sequences of length 9: twist NOT induced by Galois in %d/50 (q|h: twist is a genuine constraint)" % bad)
M2 = CyclotomicField(36, 'v'); v = M2.gen(); i4 = v**9; z9 = v**4
bad2 = 0
for trial in range(50):
    b = [i4**randint(0, 3) for y in range(9)]
    X1 = sum(b[y] * z9**y for y in range(9))
    for j in [2, 4, 5, 7, 8]:
        s = crt(1, j, 4, 9)
        if M2.hom([v**s])(X1) != sum(b[y] * z9**(j*y) for y in range(9)): bad2 += 1
print("random mu_4-sequences of length 9 (q=3 ∤ h=4): failures of X(zeta^j)=tau_j X(zeta): %d/250 (identity, by Prop D1)" % bad2)
