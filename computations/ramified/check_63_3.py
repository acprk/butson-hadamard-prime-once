#!/usr/bin/env python3
"""Is (n,h) = (63,3) excluded by a result used for Do Duc's list [arXiv:1903.07334v2, Remark 3.13]?

Do Duc's list of 2687 open pairs is what remains after Results 1.1-1.4, Result 1.5 and
Theorems 3.2, 3.3, 3.7, 3.11 of that paper.  We evaluate each of them at (63,3).
Input (paths relative to the artifact root): computations/count2262/DoDuc_BH_open_cases.txt,
or a path given as argv[1].  This script lives in computations/ramified/ of the artifact.
"""
import os
import re
import sys
from fractions import Fraction

from fdesc import fac, order, selfconj
from ramified_new import duc37, fdescent

n, h = 63, 3
m = 63                          # lcm(n, h)
here = os.path.dirname(os.path.abspath(__file__))
root = os.path.normpath(os.path.join(here, '..', '..'))    # artifact root
# Artifact layout first; the second entry is the same file in the development tree.
CANDIDATES = [os.path.join(root, 'computations', 'count2262', 'DoDuc_BH_open_cases.txt'),
              os.path.join(root, 'release', 'review', 'count2262', 'DoDuc_BH_open_cases.txt')]
if len(sys.argv) > 1:
    fn = sys.argv[1]
else:
    fn = next((c for c in CANDIDATES if os.path.exists(c)), None)
    if fn is None:
        sys.exit('DoDuc_BH_open_cases.txt not found; expected computations/count2262/ '
                 'under the artifact root, or pass its path as argv[1]')
txt = open(fn).read()
pairs = {(int(a), int(b)) for a, b in re.findall(r'(\d+)\s*,\s*(\d+)', txt)}
print('pairs in list:', len(pairs), ' (63,3) in list:', (63, 3) in pairs)
print('pairs (63,h) in list:', sorted(b for a, b in pairs if a == 63))

print('Result 1.1(1) BH(Z_{2p^2},2p): n=2p^2?', False)
print('Result 1.1(2) Ma-Ng BH(Z_{3pq},3), p,q>3 distinct primes: 63 = 3*3*7 -> needs p,q>3:', False)
print('Result 1.1(3) BH(Z_{p+q},pq): h=3 is not pq:', False)
print('Result 1.2(i) h=2:', False, '; (ii) n=p+2 with p prime -> 61 prime, but h=3 is not 2p^b:', False,
      '; (iii) n=2q:', False)
print('Result 1.3 Lam-Leung: 63 in 3N:', 63 % 3 == 0, '-> no exclusion')
sqf = 1
for r, e in fac(n).items():
    if e % 2:
        sqf *= r
print('Result 1.4 Brock: square-free part', sqf, '; primes r of it with r not dividing h and r^j=-1 mod h:',
      [r for r in fac(sqf) if h % r and any(pow(r, j, h) == h - 1 for j in range(1, h + 1))])
print('Thm 3.2 needs every prime of n to divide h: 7 | 3?', False, '-> not applicable')
print('Thm 3.3: primes r | n, r not dividing h, self-conjugate mod 63:',
      [r for r in fac(n) if h % r and selfconj(r, m)], '(ord_9 7 =', order(7, 9), ')')
print('Thm 3.7 witness:', duc37(n, h), '(u = 9: w = 3 <= 2^0 * (3,9) * 1 = 3)')
f = order(7, 3)
M = 7
print('Thm 3.11 (h=3^1, |G|=3^2*7, m=7 non-square): f = ord_3 7 =', f, 'odd;',
      'f<=m:', f <= M, '; 3 <= m^2+m+1:', 3 <= M * M + M + 1, '-> no exclusion')
print('Schmidt field-descent bound (not used by Do Duc):', fdescent(n, h))
print('Theorem S of this paper: 7 || 63 and 7 does not divide 3 -> excluded')
