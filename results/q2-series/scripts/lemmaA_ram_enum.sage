# Independent COMPLETE enumeration test of Lemma A.
#   p odd prime, p∤d, K = Q(zeta_p, zeta_d) = Q(zeta_{pd}), O = Z[zeta_{pd}], n in Z with v_p(n) = 1.
#   All F in O[C_p] with F F^* = n correspond bijectively to tuples (f_0..f_{p-1}), f_j = F(zeta_p^j),
#   with f_j * conj(f_j) = n and u_a = (1/p) sum_j zeta_p^{-ja} f_j in O for all a.
#   Each f_j ranges over the complete list norm_elements(K, n). Up to the symmetries
#   (f_j) -> (w f_j) (w in mu_K) and (f_j) -> (zeta_p^{jk} f_j) (shift of F), which preserve
#   the Lemma A conclusion, f_0 is an orbit representative and f_1 is taken mod mu_p.
#   Meet-in-the-middle on a random linear compression of the integrality condition mod p,
#   every hit is re-verified exactly (F integral and F F^* = n in the group ring).
# usage: sage lemmaA_ram_enum.sage p d n [seed] [neg]   (p | d allowed: ramified coefficients, Lemma A')
import sys, numpy as np, random
import os
load(os.path.join(os.path.dirname(os.path.abspath(sys.argv[0])), 'norm_elements.sage'))
p = int(sys.argv[1]); d = int(sys.argv[2]); n = int(sys.argv[3])
seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
NEG = len(sys.argv) > 5 and sys.argv[5] == 'neg'
assert p % 2 == 1 and is_prime(p) and (valuation(n, p) == 1 or NEG)
# d MAY be divisible by p (ramified coefficients, e(P|p) = phi(p^a))
N = p*d if d > 1 else p
print('e(P|p) =', euler_phi(p**valuation(N,p)), ' v_P(n) should be', valuation(n,p)*euler_phi(p**valuation(N,p)))
K.<z> = CyclotomicField(N); phi = K.degree()
zp = z^(N//p)
Pp = K.primes_above(p)
print("p=%d d=%d n=%d  [K:Q]=%d  #P|p=%d  P==Pbar: %s" % (p, d, n, phi, len(Pp),
      [P == K.ideal([g.conjugate() for g in P.gens()]) for P in Pp]))
C = norm_elements(K, n, verbose=True)
cands = [g for (ex, g) in C]
nc = len(cands)
print("complete list of norm-n elements:", nc, " ideal patterns:", sorted(set(ex for ex, g in C)))
# P-adic valuations of candidates
vals = [tuple(K.ideal(g).valuation(P) for P in Pp) for g in cands]
# orbit reps
idx = {g: i for i, g in enumerate(cands)}
tg = K(K.unit_group().torsion_generator().value()); o = tg.multiplicative_order()
muK = [tg^k for k in range(o)]
reps0 = []; seen = set()
for i, g in enumerate(cands):
    if i in seen: continue
    reps0.append(i)
    for w in muK: seen.add(idx[w*g])
reps1 = []; seen = set()
for i, g in enumerate(cands):
    if i in seen: continue
    reps1.append(i)
    for k in range(p): seen.add(idx[zp^k*g])
print("f_0 reps:", len(reps0), " f_1 reps:", len(reps1))
# integrality vectors mod p
Wd = p*phi
def vec(x): return [int(c) % p for c in x.list()]
V = np.zeros((nc, p, Wd), dtype=np.int64)
for c, g in enumerate(cands):
    for j in range(p):
        row = []
        for a in range(p):
            row += vec(zp^((-j*a) % p) * g)
        V[c, j] = row
t = int(ceil(70/log(p, 2).n()))
rng = np.random.default_rng(int(seed))
R = rng.integers(0, p, size=(Wd, t), dtype=np.int64)
CV = (V @ R) % p                         # (nc, p, t)
pw = np.array([int(pow(p, i, 2**63)) for i in range(t)], dtype=np.uint64)
def key(A): return ((A % p).astype(np.uint64) * pw).sum(axis=1, dtype=np.uint64)
L = (p+1)//2
def expand(acc, ids, j, allowed):
    sub = CV[allowed, j, :]
    acc2 = (acc[:, None, :] + sub[None, :, :]).reshape(-1, t) % p
    ids2 = np.concatenate([np.repeat(ids, len(allowed), axis=0),
                           np.tile(np.array(allowed), ids.shape[0])[:, None]], axis=1)
    return acc2, ids2
allr = list(range(nc))
# right side
acc = np.zeros((1, t), dtype=np.int64); ids = np.zeros((1, 0), dtype=np.int64)
for j in range(L, p): acc, ids = expand(acc, ids, j, allr)
kR = key((-acc) % p); order = np.argsort(kR); kR = kR[order]; idsR = ids[order]
print("right side:", len(kR))
sols = []
for c0 in reps0:
    acc = CV[c0, 0][None, :].copy(); ids = np.array([[c0]])
    acc, ids = expand(acc, ids, 1, reps1)
    for j in range(2, L): acc, ids = expand(acc, ids, j, allr)
    kL = key(acc)
    lo = np.searchsorted(kR, kL, 'left'); hi = np.searchsorted(kR, kL, 'right')
    for i in np.nonzero(hi > lo)[0]:
        for r in range(lo[i], hi[i]):
            sols.append(list(ids[i]) + list(idsR[r]))
print("MITM hits:", len(sols))
good = 0; viol = 0; nontriv = 0; valpat = {}
from collections import Counter
valpat = Counter()
for s in sols:
    f = [cands[c] for c in s]
    if any(int(x) % p for x in (sum(V[s[j], j] for j in range(p)))): continue   # false positive
    u = [sum(zp^((-j*a) % p)*f[j] for j in range(p))/p for a in range(p)]
    assert all(x.is_integral() for x in u)
    for sh in range(1, p):
        assert sum(u[a]*u[(a+sh) % p].conjugate() for a in range(p)) == 0
    assert sum(x*x.conjugate() for x in u) == n
    good += 1
    if sum(1 for x in u if x != 0) > 1: nontriv += 1
    vs = [vals[c] for c in s]
    valpat[tuple(vs[0])] += 1
    bad = len(set(vs)) != 1
    if not bad:
        for k, P in enumerate(Pp):
            for j in range(1, p):
                if f[j] != f[0] and K.ideal(f[j]-f[0]).valuation(P) <= vs[0][k]:
                    bad = True
    if bad:
        viol += 1
        if viol <= 5: print("VIOLATION:", s, vs)
print("verified F with F F* = n (up to symmetry):", good, " non-monomial:", nontriv)
print("valuation vectors (v_P(f_0))_P -> count:", dict(valpat))
print("Lemma A violations:", viol)
