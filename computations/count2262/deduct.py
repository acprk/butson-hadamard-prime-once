#!/usr/bin/env python3
"""Deduct from Do Duc's open list the pairs covered by earlier criteria.

Inputs (shipped next to this script, no other files are read):
  DoDuc_BH_open_cases.txt  Do Duc's list of open pairs (n,h), n,h <= 100, referenced in
                           [DoDuc2019, Remark 3.13] (personal.ntu.edu.sg/bernhard/BH/BH_open_cases.txt),
                           format "[n, h; n, h; ...]".
  hs_table1.txt            transcription of Hiranandani-Schlenker 2016, Table 1 (n,l <= 15),
                           one cell per line: "n l entry".
Artifact location: computations/count2262/ (relative to the artifact root); all inputs and
outputs are resolved relative to this script's directory, not the working directory.
Outputs (written next to this script):
  remaining_2262.txt, remaining_61.txt, covered_with_reason.txt.

Expected: |P| = 2687; classes 2262 and 61; covered 237 and 23; remaining 2025 and 38.
"""
import os
import re
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))


def path(name):
    return os.path.join(HERE, name)


def factorint(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def isprime(n):
    return n > 1 and factorint(n) == {n: 1}


# --- Do Duc's list -----------------------------------------------------------------
def read_doduc(fn):
    txt = open(fn, encoding='utf-8').read().strip()
    if not (txt.startswith('[') and txt.endswith(']')):
        sys.exit(f'{fn}: expected a list enclosed in [ ]')
    pairs = []
    for k, item in enumerate(txt[1:-1].split(';')):
        item = item.strip()
        if not item:
            continue
        m = re.fullmatch(r'(\d+)\s*,\s*(\d+)', item)
        if not m:
            sys.exit(f'{fn}: cannot parse item {k}: {item!r}')
        n, h = int(m.group(1)), int(m.group(2))
        if not (1 <= n <= 100 and 1 <= h <= 100):
            sys.exit(f'{fn}: pair out of range: {(n, h)}')
        pairs.append((n, h))
    if len(set(pairs)) != len(pairs):
        dup = [x for x, c in Counter(pairs).items() if c > 1]
        sys.exit(f'{fn}: duplicate pairs {dup}')
    return set(pairs)


# --- Hiranandani-Schlenker Table 1 --------------------------------------------------
def read_hs(fn):
    HS = {}
    for ln, line in enumerate(open(fn, encoding='utf-8'), 1):
        line = line.split('#', 1)[0].strip()
        if not line:
            continue
        parts = line.split()
        if len(parts) != 3:
            sys.exit(f'{fn}:{ln}: expected "n l entry"')
        n, l, v = int(parts[0]), int(parts[1]), parts[2]
        if (n, l) in HS:
            sys.exit(f'{fn}:{ln}: duplicate cell {(n, l)}')
        HS[(n, l)] = v
    if set(HS) != {(n, l) for n in range(2, 16) for l in range(2, 16)}:
        sys.exit(f'{fn}: table must have exactly the cells 2<=n,l<=15')
    return HS


P = read_doduc(path('DoDuc_BH_open_cases.txt'))
assert len(P) == 2687, len(P)
HS = read_hs(path('hs_table1.txt'))
# a cell excludes BH(n,l) if it shows an obstruction (x, xl, xh, xs, xt, xpq) or the count 0
HSex = {k for k, v in HS.items() if v.startswith('x') or v == '0'}


def S(n, h):
    return any(e == 1 and h % p for p, e in factorint(n).items())


def Ssharp(n, h):
    return S(n, h) or (n % 4 == 2 and h % 4 != 0)


L2262 = sorted(x for x in P if S(*x))
assert len(L2262) == 2262
L61 = sorted(x for x in P if Ssharp(*x) and not S(*x))
assert len(L61) == 61

# --- Yayla, Table 2 (arXiv:1408.6883v2, Appendix A; Adv. Math. Commun. 10 (2016)) -----
# Table 2 lists, for every 2 <= n <= 100 and every prime p | n, the status of p-ary perfect
# sequences (type gamma = 0) of period n.  Its Section 3 states: "For n <= 100, Theorem 2
# excludes the existence at all other pairs (n,p) except a few undecided cases" -- the eleven
# pairs below (all other pairs being p = n or n = p^2, where sequences exist and which are not
# on Do Duc's list).  Hence every pair (n,h) with h an odd prime, h | n, n <= 100, of Do Duc's
# list is excluded by Yayla's table unless it is one of the eleven.  (Pairs with h prime and
# h not dividing n do not occur among the 2262 + 61 pairs, so no rule is needed for them;
# h = 2 does not occur either.)
yayla_undec = {(28, 7), (33, 11), (39, 13), (55, 11), (56, 7), (63, 3), (69, 23), (84, 3),
               (92, 23), (95, 19), (99, 11)}
later = {(28, 7): 'Feng-Xiang 2008', (92, 23): 'Feng-Xiang 2008', (33, 11): 'LSZ 2023 Thm 6.5',
         (69, 23): 'LSZ 2023 Thm 6.5', (95, 19): 'LSZ 2023 Thm 6.5'}
assert not any(h == 2 or (isprime(h) and n % h) for n, h in L2262 + L61)


def prior(n, h):
    r = []
    if h == 4:
        r.append('h=4 (Arasu 2011 remark: N<=1000 only 1,2,4,8,16 and 11 listed orders >=260)')
    if isprime(h) and h > 2 and n % h == 0:
        if (n, h) not in yayla_undec:
            r.append('h odd prime: Yayla 2016 Table 2')
        elif (n, h) in later:
            r.append(later[(n, h)])
    if (n, h) in HSex:
        r.append('Hiranandani-Schlenker Table 1: ' + HS[(n, h)])
    return r


# --- Turyn's argument with the principal character: p^odd || n, p self-conjugate mod h ------
def selfconj(p, m):
    while m % p == 0:
        m //= p
    if m <= 2:
        return True
    y = p % m
    for _ in range(m):
        if y == m - 1:
            return True
        y = y * p % m
    return False


def unram(p, h):
    return h % p != 0 or (p == 2 and h % 4 == 2)


def turyn0(n, h):
    return any(e % 2 == 1 and unram(p, h) and selfconj(p, h) for p, e in factorint(n).items())


# --- generalized bent functions of type [1,q] (only relevant for the 61 class): Pei 1993
# (14,14), Ying-Deng 2026 (42,42) [N=21=3*7], Ikeda 1999 (every prime of N self-conjugate mod N)
gbf = {(14, 14): 'Pei 1993', (42, 42): 'Ying-Deng 2026', (30, 30): 'Ikeda 1999',
       (70, 70): 'Ikeda 1999', (90, 90): 'Ikeda 1999', (98, 98): 'Ikeda 1999'}


def prior_all(n, h):
    r = prior(n, h)
    if turyn0(n, h):
        r = r + ['Turyn principal character']
    if (n, h) in gbf:
        r = r + [gbf[(n, h)]]
    return r


print('|P| =', len(P), ' class 2262:', len(L2262), ' class 61:', len(L61))
print('HS cells in 2262:', sorted(x for x in L2262 if x in HSex))
print('Yayla-undecided pairs in 2262:', sorted(x for x in L2262 if x in yayla_undec))
print()
print('=== SUMMARY ===')
res = {}
for name, L in (('2262', L2262), ('61', L61)):
    cov = [x for x in L if prior_all(*x)]
    rem = [x for x in L if not prior_all(*x)]
    res[name] = (len(cov), len(rem))
    print(name, ': covered by an identified earlier result:', len(cov), ' not covered:', len(rem))
    fam = Counter()
    for x in cov:
        for r in prior_all(*x):
            fam[r.split(':')[0].split(' (')[0]] += 1
    for k, v in fam.most_common():
        print('    (with overlaps)', k, v)
    with open(path(f'remaining_{name}.txt'), 'w') as fo:
        fo.write(''.join(f'{n},{h}\n' for n, h in rem))
with open(path('covered_with_reason.txt'), 'w') as fo:
    for x in L2262 + L61:
        r = prior_all(*x)
        if r:
            fo.write(f'{x[0]},{x[1]}\t' + ' | '.join(r) + '\n')
assert res == {'2262': (237, 2025), '61': (23, 38)}, res
print('remaining total:', res['2262'][1] + res['61'][1])
