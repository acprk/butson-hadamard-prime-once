#!/usr/bin/env python3
"""Fresh, stdlib-only implementation of Schmidt's descent exponent F(m,n) and of the
nonexistence criteria for circulant BH(N,4) (perfect quaternary sequences), N = 0 mod 4.

Written 2026-10-09 directly from the PDFs; shares no code with
reviews/E-coding/NEWTHEORY/{fverify_indep,table5000}.

  F_A : Leung-Schmidt, DCC 36 (2005), Def. 2.6 (literal: b_i = least b in [1,c_i] such that
        for every q in D(n) one of (a),(b),(c) holds).
  F_B : Leung-Schmidt, DCC 64 (2012), Def. 2.10 (closed form, gcd(m, prod p^{b(p,m,n)})).
"""
from fractions import Fraction
from functools import lru_cache
from math import gcd

LIM = 4_100_000
_spf = None


def _sieve():
    global _spf
    if _spf is None:
        spf = list(range(LIM + 1))
        i = 2
        while i * i <= LIM:
            if spf[i] == i:
                for j in range(i * i, LIM + 1, i):
                    if spf[j] == j:
                        spf[j] = i
            i += 1
        _spf = spf
    return _spf


def fac(n):
    """prime factorisation as dict; trial division beyond the sieve."""
    f = {}
    if n <= LIM:
        spf = _sieve()
        while n > 1:
            p = spf[n]
            f[p] = f.get(p, 0) + 1
            n //= p
        return f
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def vp(p, x):
    k = 0
    while x % p == 0:
        x //= p
        k += 1
    return k


def phi(n):
    r = n
    for p in fac(n):
        r = r // p * (p - 1)
    return r


def carmichael(n):
    l = 1
    for p, e in fac(n).items():
        if p == 2:
            t = 1 if e == 1 else (2 if e == 2 else 2 ** (e - 2))
        else:
            t = (p - 1) * p ** (e - 1)
        l = l * t // gcd(l, t)
    return l


@lru_cache(maxsize=None)
def order(a, n):
    """multiplicative order of a mod n (n >= 1), via divisors of Carmichael lambda."""
    if n == 1:
        return 1
    assert gcd(a, n) == 1
    o = carmichael(n)
    for p in fac(o):
        while o % p == 0 and pow(a, o // p, n) == 1:
            o //= p
    return o


def m_q(m, q):
    P = fac(m)
    if m % 2 == 1 or q == 2:
        r = 1
        for p in P:
            if p != q:
                r *= p
    else:
        r = 4
        for p in P:
            if p != 2 and p != q:
                r *= p
    return r


def F_A(m, n):
    Pm, Dn = fac(m), list(fac(n))
    F = 1
    for p, c in Pm.items():
        for b in range(1, c + 1):
            good = True
            for q in Dn:
                ca = (q == p) and (p, b) != (2, 1)
                cb = (b == c)
                cc = (q != p) and pow(q, order(q, m_q(m, q)), p ** (b + 1)) != 1
                if not (ca or cb or cc):
                    good = False
                    break
            if good:
                break
        else:
            raise AssertionError("b=c always satisfies (b)")
        F *= p ** b
    return F


def F_B(m, n):
    Dm, Dn = list(fac(m)), list(fac(n))
    prod = 1
    for r in Dm:
        others = [q for q in Dn if q != r]
        if not others:            # D(n) = {r}  (D(n) is never empty since n > 1)
            b = 2 if r == 2 else 1
        elif r == 2:
            b = max(vp(2, q * q - 1) + vp(2, order(q, m_q(m, q))) - 1 for q in others)
        else:
            b = max(vp(r, q ** (r - 1) - 1) + vp(r, order(q, m_q(m, q))) for q in others)
        prod *= r ** b
    return gcd(m, prod)


def schmidt_bound(C, F):
    return Fraction(C * C * F * F, 4 * phi(F))


# ---------------------------------------------------------------- criteria for BH(Z_N, 4)
def selfconj(p, M):
    """p self-conjugate mod M (Duc 2020 Def 2.5): -1 in <p> mod M', M' = p-free part of M.
    Uses: a cyclic group has at most one involution, so -1 in <p> iff ord even and p^(ord/2) = -1."""
    while M % p == 0:
        M //= p
    if M <= 2:
        return True
    o = order(p, M)
    return o % 2 == 0 and pow(p, o // 2, M) == M - 1


def lcm(a, b):
    return a * b // gcd(a, b)


def divisors(f):
    ds = [1]
    for p, e in f.items():
        ds = [d * p ** k for d in ds for k in range(e + 1)]
    return ds


def criteria(N):
    """returns dict name -> witness (or None). N = 0 mod 4."""
    f = fac(N)
    out = {}
    out["2sq"] = next((p for p, e in f.items() if p % 4 == 3 and e % 2), None)
    out["DS(2^a,a>=5)"] = f[2] if (len(f) == 1 and f[2] >= 5) else None
    L = lcm(4, N)
    out["Turyn/Duc3.3"] = next((p for p in f if p > 2 and selfconj(p, L)), None)
    out["S(odd p^1)"] = next((p for p, e in f.items() if p > 2 and e == 1), None)
    # Duc 2020 Thm 3.7 with h=4 (only the 2-part can be self-conjugate once Turyn/Duc3.3 fails;
    # we implement it in general anyway)
    u = 1
    for p, e in f.items():
        if selfconj(p, L):
            u *= p ** e
    k = 1
    for p, e in fac(u).items():
        if e % 2:
            k *= p
    w2 = u // k
    w = int(round(w2 ** 0.5))
    assert w * w == w2
    t, r = 1, len(fac(k))        # t = #primes of h=4
    hu = gcd(4, u)
    if k % 2:
        expo = t - r - 1 + (1 if r == t else 0)
        rhs2 = Fraction(4) ** expo * hu * hu * Fraction(k, phi(k))   # (rhs)^2, expo may be <0
    else:
        expo = t - r - 1
        rhs2 = Fraction(4) ** expo * hu * hu * Fraction(2 * k, phi(k))
    out["Duc3.7"] = (u, w) if w * w > rhs2 else None
    # Schmidt F-bound over all character orders d | N, both F definitions
    strict, equal = [], []
    for d in divisors(f):
        Ld = lcm(4, d)
        C = 4 * N // Ld
        for name, Ff in (("A", F_A), ("B", F_B)):
            F = Ff(Ld, N)
            b = schmidt_bound(C, F)
            if b < N:
                strict.append((d, C, name, F, b))
            elif b == N and any(q % 2 for q in fac(F)):
                equal.append((d, C, name, F))
    out["Fstrict"] = strict[0] if strict else None
    out["Feq(L5.7)"] = equal if equal else None
    return out


OTHER = ["2sq", "DS(2^a,a>=5)", "Turyn/Duc3.3", "S(odd p^1)", "Duc3.7", "Fstrict"]


def criteria_cheap(N):
    f = fac(N)
    L = lcm(4, N)
    return {"2sq": next((p for p, e in f.items() if p % 4 == 3 and e % 2), None),
            "DS(2^a,a>=5)": f[2] if (len(f) == 1 and f[2] >= 5) else None,
            "Turyn/Duc3.3": next((p for p in f if p > 2 and selfconj(p, L)), None),
            "S(odd p^1)": next((p for p, e in f.items() if p > 2 and e == 1), None)}
