"""Which affine maps x -> t x + s of C_{q^2} are beta-conjugate to affine maps of C_q x C_q (beta(i+qj)=(i,j))."""
import itertools
def is_affine_qq(f, q):
    # f: dict (i,j)->(i',j'); affine iff f(v)-f(0) additive
    o = f[(0, 0)]
    lin = {v: ((f[v][0] - o[0]) % q, (f[v][1] - o[1]) % q) for v in f}
    for u in f:
        for v in f:
            w = ((u[0] + v[0]) % q, (u[1] + v[1]) % q)
            if lin[w] != ((lin[u][0] + lin[v][0]) % q, (lin[u][1] + lin[v][1]) % q): return None
    return lin[(1, 0)], lin[(0, 1)], o
for q in (2, 3, 5, 7):
    n = q * q; beta = lambda x: (x % q, x // q); binv = lambda v: v[0] + q * v[1]
    comp = []
    for t in range(n):
        for s in range(n):
            f = {beta(x): beta((t * x + s) % n) for x in range(n)}
            r = is_affine_qq(f, q)
            if r: comp.append((t, s, r))
    ts = sorted(set((t % q, t // q) for t, s, r in comp)); ss = sorted(set((s % q) for t, s, r in comp))
    print('q=%d: #beta-affine (t,s) = %d of %d;  t0 values %s ; s0 values %s' % (q, len(comp), n * n, sorted(set(a for a, b in ts)), ss))
    for t, s, r in comp:
        if t == 1 + q and s == 0: print('   x->(1+q)x  <->  linear map e1->%s e2->%s (shear)' % (r[0], r[1]))
    units_nonaff = [t for t in range(n) if t % q and not any(tt == t for tt, _, _ in comp)]
    print('   units t NOT beta-affine for any s:', units_nonaff)
print('--- per-unit-t list of shifts s making x->tx+s beta-affine, and translations')
for q in (3, 5):
    n = q * q; beta = lambda x: (x % q, x // q)
    for t in [1, q - 1, 1 + q, 2]:
        S = [s for s in range(n) if is_affine_qq({beta(x): beta((t * x + s) % n) for x in range(n)}, q)]
        print('q=%d t=%d : beta-affine for s in %s' % (q, t, S))
