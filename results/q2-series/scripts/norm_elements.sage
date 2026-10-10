# Shared helpers (independent re-implementation, 2026-10-09).
# norm_elements(K, n): COMPLETE list of x in O_K (K cyclotomic, CM) with x * conj(x) == n.
#   Method: enumerate every ideal I with I*conj(I) = (n) (exponent vectors over primes above n),
#   keep principal ones, normalise the generator by a unit u with u*conj(u) = g*conj(g)/n
#   (solved exactly with the unit-group log map), then multiply by all roots of unity.
#   Completeness: any x with x xbar = n generates such an I; two generators differ by a unit eps
#   with eps*conj(eps) = 1, i.e. |eps| = 1 in every embedding (abelian field) => root of unity.
import itertools

def conj(x):
    return x.conjugate()

def norm_elements(K, n, verbose=False):
    n = ZZ(n)
    O = K.ring_of_integers()
    plist = []
    for (q, _) in n.factor():
        for P in K.primes_above(q):
            plist.append(P)
    # conjugation pairs
    def cP(P): return K.ideal([conj(g) for g in P.gens()])
    vn = {P: K.ideal(n).valuation(P) for P in plist}
    pairs = []; used = []
    for P in plist:
        if any(P == U for U in used): continue
        Q = cP(P); used += [P, Q]
        pairs.append((P, Q))
    choices = []
    for (P, Q) in pairs:
        if P == Q:
            if vn[P] % 2: return []      # self-conjugate prime with odd exponent: no element
            choices.append([vn[P]//2])
        else:
            choices.append(list(range(vn[P]+1)))
    UG = K.unit_group()
    fu = [K(u) for u in UG.fundamental_units()]
    r = len(fu)
    if r > 0:
        M = matrix(QQ, [UG.log(u*conj(u))[1:] for u in fu])   # rows: log of u ubar
    out = []
    tg = K(UG.torsion_generator().value()); o = tg.multiplicative_order()
    mu = [tg^k for k in range(o)]
    for ex in itertools.product(*choices):
        I = K.ideal(1)
        for (P, Q), a in zip(pairs, ex):
            I = I * P^a * (Q^(vn[P]-a) if P != Q else 1)
        if not I.is_principal():
            if verbose: print("  non-principal", ex)
            continue
        g = K(I.gens_reduced()[0])
        t = g*conj(g)/n
        if t != 1:
            if r == 0:
                continue
            lt = vector(QQ, UG.log(t)[1:])
            try:
                sol = M.solve_left(lt)
            except ValueError:
                continue
            if any(s not in ZZ for s in sol):
                if verbose: print("  generator not normalisable", ex)
                continue
            u = prod(f^ZZ(s) for f, s in zip(fu, sol))
            g = g/u
            t = g*conj(g)/n
            if t != 1:
                # may differ by torsion (cannot for a positive real), report
                raise RuntimeError("normalisation failed")
        assert g*conj(g) == n
        out.append((ex, g))
    res = []
    for ex, g in out:
        for w in mu:
            res.append((ex, w*g))
    return res
