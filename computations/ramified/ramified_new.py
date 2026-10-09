#!/usr/bin/env python3
"""Which lengths pq^e <= NMAX (p odd prime, q != p prime, e >= 2) of perfect p-ary sequences
(circulant BH(pq^e, p)) are excluded by Theorem C but by none of the earlier criteria below?

Artifact location: computations/ramified/ (relative to the artifact root); the output
ramified_new_<NMAX>.txt is written next to this script, independent of the working directory.

Stdlib only; uses fdesc.py (descent exponents F_A = Leung-Schmidt 2005 Def. 2.6 and
F_B = Leung-Schmidt 2012 Def. 2.10) from this directory.

Earlier criteria, translated to n = pq^e, h = p, f = ord_p(q):
  DD3.3   Do Duc [DCC 88 (2020)] Thm 3.3: a prime divisor r of n with r not dividing h and r
          self-conjugate modulo lcm(n,h) divides h.  Here: q self-conjugate modulo p.
          (This contains LSZ23 Thm 5.1(a) and 5.3, Ma-Ng 2009 as quoted by Lv 2017, Brock's
          condition and Do Duc Thm 3.11(i) for these parameters.)
  DD3.7   Do Duc Thm 3.7 (general form, as in fdesc.criteria with h in place of 4).
  DD3.11  Do Duc Thm 3.11(ii),(iii) with h = p^1, |G| = p*m, m = q^e not a square (e odd).
          (iii) is LSZ23 Thm 5.1(b) for these parameters.
  LSZ5.4  LSZ23 Thm 5.4 (m = q^e, n = p, r = q^e, s = 1): e even, v1 = q^{e/2} if f odd,
          v1 = 1 if f even; if v1 = 1 or f > 2 v1 - 1 then p <= q^{e/2} + 1.
  F-P8    Feng 2009 Prop. 8: q^e is a square modulo p.
  F-P5    Feng 2009 Prop. 5: p = 5 implies q^e = 1 mod 5.
  FX08    Feng-Xiang 2008: q^e in {2, 4} excluded.
  LF16    Liu-Feng 2016 as quoted in Lv 2017, list item (2): p = 3 mod 4, gcd(q-1,p) = 1,
          (q/p) = 1, f odd, l = e odd, n' = 1, l < lambda/s with s = (p-1)/f and lambda the
          least odd integer with x^2 + p y^2 = 4 q^lambda solvable.
  Lv1.5   Lv 2017 Thm 1.5: (p, f, l0) in the list, e odd <= l0, Xi_p has no root mod q.
          (Lv Thm 1.3 needs q to divide the length exactly once: not applicable.)
  Fdesc   Schmidt's field-descent bound: for every d | n, L = lcm(h,d), C = nh/L,
          n > C^2 F^2 / (4 phi(F)) with F = F_A(L,n) or F_B(L,n) excludes.
Theorem S of this paper does not apply (only p divides n exactly once, and p | h).

Usage: python3 ramified_new.py [NMAX]      (default 2000)
"""
import os
import sys
from fractions import Fraction
from math import gcd, isqrt

import fdesc
from fdesc import F_A, F_B, fac, order, phi, schmidt_bound, selfconj, divisors


def primes_upto(N):
    return [x for x in range(2, N + 1) if all(x % d for d in range(2, isqrt(x) + 1))]


def lcm(a, b):
    return a * b // gcd(a, b)


def is_square_mod(a, p):
    a %= p
    return a == 0 or pow(a, (p - 1) // 2, p) == 1


def duc37(n, h):
    """Do Duc 2020 Thm 3.7 for BH(Z_n, h); returns witness or None."""
    m = lcm(n, h)
    u = 1
    for r, e in fac(n).items():
        if selfconj(r, m):
            u *= r ** e
    k = 1
    for r, e in fac(u).items():
        if e % 2:
            k *= r
    w2 = u // k
    w = isqrt(w2)
    assert w * w == w2
    t, rr = len(fac(h)), len(fac(k))
    hu = gcd(h, u)
    if k % 2:
        expo = t - rr - 1 + (1 if rr == t else 0)
        rhs2 = Fraction(4) ** expo * hu * hu * Fraction(k, phi(k))
    else:
        expo = t - rr - 1
        rhs2 = Fraction(4) ** expo * hu * hu * Fraction(2 * k, phi(k))
    return (u, w) if w * w > rhs2 else None


def fdescent(n, h):
    for d in divisors(fac(n)):
        L = lcm(h, d)
        C = n * h // L
        for name, Ff in (('A', F_A), ('B', F_B)):
            F = Ff(L, n)
            if schmidt_bound(C, F) < n:
                return (d, name, F)
    return None


def least_lambda(p, q, cap=99):
    for lam in range(1, cap + 1, 2):
        R = 4 * q ** lam
        y = 0
        while p * y * y <= R:
            x2 = R - p * y * y
            if isqrt(x2) ** 2 == x2:
                return lam
            y += 1
    return None


XI = {31: [1, 0, 1, -1], 127: [1, -1, -2, 1, 3, -1], 139: [1, -1, 1, 2],
      151: [1, -1, 1, 0, 3, -1, 3, 1]}          # coefficients, highest degree first
LV15 = [(31, 5, 1), (127, 9, 1), (127, 21, 3), (139, 23, 1), (151, 15, 3)]


def xi_has_root(p, q):
    c = XI[p]
    return any(sum(a * pow(x, len(c) - 1 - i, q) for i, a in enumerate(c)) % q == 0
               for x in range(q))


def criteria(p, q, e):
    n, h, f, Q = p * q ** e, p, order(q, p), q ** e
    out = []
    if selfconj(q, p):
        out.append('DD3.3')
    if duc37(n, h):
        out.append('DD3.7')
    if e % 2 == 1:
        if f > Q and p > Fraction(f * f - Q, f - Q):
            out.append('DD3.11(ii)')
        if p > Q * Q + Q + 1:
            out.append('DD3.11(iii)=LSZ5.1(b)')
    else:
        v1 = 1 if f % 2 == 0 else q ** (e // 2)
        if (v1 == 1 or f > 2 * v1 - 1) and p > q ** (e // 2) + 1:
            out.append('LSZ5.4')
    if not is_square_mod(Q, p):
        out.append('Feng-P8')
    if p == 5 and Q % 5 != 1:
        out.append('Feng-P5')
    if Q in (2, 4):
        out.append('FX08')
    if (p % 4 == 3 and gcd(q - 1, p) == 1 and is_square_mod(q, p) and f % 2 == 1
            and e % 2 == 1):
        lam = least_lambda(p, q)
        s = (p - 1) // f
        if lam is not None and e < Fraction(lam, s):
            out.append('LF16')
    for (pp, ff, l0) in LV15:
        if p == pp and f == ff and e % 2 == 1 and e <= l0 and not xi_has_root(p, q):
            out.append('Lv1.5')
    if fdescent(n, h):
        out.append('Fdesc')
    return out


def main():
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    P = primes_upto(NMAX)
    rows = []
    for p in P:
        if p == 2:
            continue
        for q in P:
            if q == p:
                continue
            e = 2
            while p * q ** e <= NMAX:
                rows.append((p * q ** e, p, q, e, criteria(p, q, e)))
                e += 1
    rows.sort()
    new = [r for r in rows if not r[4]]
    print(f'lengths pq^e <= {NMAX}, p odd, e >= 2: {len(rows)}')
    print(f'not covered by any earlier criterion: {len(new)}')
    print('new lengths:', ', '.join(str(r[0]) for r in new))
    print('(n, p, q, e):', ' '.join(f'({n},{p},{q},{e})' for n, p, q, e, _ in new))
    from collections import Counter
    c = Counter()
    for r in rows:
        for x in r[4]:
            c[x] += 1
    print('criteria hits (with overlaps):', dict(c))
    only = Counter(r[4][0] for r in rows if len(r[4]) == 1)
    print('pairs excluded by exactly one criterion:', dict(only))
    sc = [r for r in rows if 'DD3.3' in r[4]]
    print('covered by Do Duc Thm 3.3 (q self-conjugate mod p):', len(sc),
          ' e.g. (75,3):', [r[4] for r in rows if (r[0], r[1]) == (75, 3)])
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), f'ramified_new_{NMAX}.txt')
    with open(out, 'w') as fo:
        for n, p, q, e, cr in rows:
            fo.write(f'{n}\t{p}\t{q}\t{e}\t' + (','.join(cr) if cr else 'NEW') + '\n')

    # Theorem C(ii) instance (1400, 7) = 7 * 2^3 * 5^2
    n, h = 1400, 7
    m = lcm(n, h)
    print()
    print('(1400,7): primes r | n, r not dividing h, self-conjugate mod lcm(n,h):',
          [r for r in fac(n) if h % r and selfconj(r, m)], '(Do Duc 3.3 applies iff nonempty)')
    print('(1400,7): 5 self-conjugate mod 14:', selfconj(5, 14),
          '; Do Duc 3.7:', duc37(n, h), '; field descent:', fdescent(n, h))


if __name__ == '__main__':
    main()


def report_1400():
    """Hand-checkable conditions for (n,h) = (1400,7), n = 7 * 2^3 * 5^2 (Theorem C(ii), q=2, e=3, u=25)."""
    n, h, p = 1400, 7, 7
    m = n // p                                   # 200 = 2^3 5^2
    f = gcd(order(2, p), order(5, p))
    print('(1400,7): Do Duc 3.11: m=200 non-square, f=gcd(ord_7 2, ord_7 5)=', f,
          '(odd);', 'f<=m:', f <= m, '; p<=m^2+m+1:', p <= m * m + m + 1)
    print('(1400,7): LSZ 5.1(b): primes self-conj mod 7:', [r for r in (2, 5) if selfconj(r, p)],
          '; A = 1400/(7*25) = 8 non-square; 7 <= 8^2+8+1:', 7 <= 73)
    print('(1400,7): LSZ 5.3 (q=5, c=2, m\'=1, n\'=7): 5 self-conj mod 49:', selfconj(5, 49),
          '; 5*7 <= 7 + 1400/7 - 1:', 35 <= 7 + 200 - 1, '(m\'=8: 5 self-conj mod 392:',
          selfconj(5, 392), ')')
    print('(1400,7): LSZ 5.4 needs rs=200 square: False; Feng Prop 8: 200 square mod 7:',
          is_square_mod(200, 7), '; Brock: square-free part 14 is even')


if __name__ == '__main__':
    report_1400()
