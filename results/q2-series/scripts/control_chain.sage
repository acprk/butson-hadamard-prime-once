# Control for Theorem Q2': run Q2 Steps 1-6 (with Lemma A' at q=3, q^2 | h) on the genuine BH(Z_12,18) orbit reps found by bhcol.
# Expect: Lemma A' holds, Step 2 (r in k) holds (2 unramified in Q(zeta_9)), Step 3 holds, Step 4 fails (-1 in mu_18).
import sys
h = 18; q = 3; n = 12
K.<z> = CyclotomicField(36)          # contains zeta_18, i, zeta_3
zh = z^(36//h); I = z^9; z3 = z^12
P = K.primes_above(q); assert len(P) == 1; P = P[0]
e = K.ideal(q).valuation(P); print("e(P|3) =", e, " v_P(12) =", K.ideal(12).valuation(P))
tau = [s for s in K.automorphisms() if s(I) == -I and s(zh) == zh][0]
cnt = dict(A=0, step2=0, step3=0, a0=0, b0=0, kreal=0, collaw=0, gen9=0)
import os
reps = [list(map(int, l.split())) for l in open(os.path.join(os.path.dirname(os.path.abspath(sys.argv[0])), 'bh_12_18_reps.txt')) if l.strip()]
for x in reps:
    if any(v % 3 for v in x): cnt['gen9'] += 1
    C = [[zh^x[g] for g in range(n) if g % 4 == y and g % 3 == w][0] for y in range(4) for w in range(3)]
    col = lambda y, w: C[3*y + w]
    a = [col(0, w) - col(2, w) for w in range(3)]; b = [col(1, w) - col(3, w) for w in range(3)]
    fv = [sum((a[w] + I*b[w]) * z3^(j*w) for w in range(3)) for j in range(3)]
    vals = [K.ideal(v).valuation(P) for v in fv]
    okA = len(set(vals)) == 1 and all(K.ideal(fv[j] - fv[0]).valuation(P) > vals[0] for j in (1, 2))
    cnt['A'] += okA
    r = [fv[j] / fv[0] for j in range(3)]
    cnt['step2'] += all(tau(rj) == rj for rj in r)
    av = [sum(a[w] * z3^(j*w) for w in range(3)) for j in range(3)]
    bv = [sum(b[w] * z3^(j*w) for w in range(3)) for j in range(3)]
    cnt['step3'] += all(bv[0]*av[j] == av[0]*bv[j] for j in range(3))
    cnt['a0'] += all(t == 0 for t in a); cnt['b0'] += all(t == 0 for t in b)
    S = [w for w in range(3) if b[w] != 0]
    if S and all(a[w] == 0 or b[w] != 0 for w in range(3)):
        kap = [a[w] / b[w] for w in S]
        if len(set(kap)) == 1 and kap[0].conjugate() == kap[0]: cnt['kreal'] += 1
print("reps:", len(reps), cnt)
