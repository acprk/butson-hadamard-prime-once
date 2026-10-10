# Recomputes which entries of the Do Duc open list are closed by Theorems Q2, Q2', E1, E2, by testing
# each theorem's hypotheses directly, and writes the remaining list to ../../remaining-open-cases.json.
# Inputs: ../../../computations/count2262/DoDuc_BH_open_cases.txt (Do Duc 2019, Remark 3.13; n,h <= 100)
#         ../data/remaining_before_q2_series.json (entries not excluded by our earlier criteria; see its description)
# usage: python3 closed_entries.py            (stdlib only)
import json, os, re
from math import gcd
from decomp import info, vp, lcm          # decomposition-group test used by Theorem E2

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..', '..', '..')
txt = open(os.path.join(ROOT, 'computations', 'count2262', 'DoDuc_BH_open_cases.txt')).read()
DODUC = set((int(a), int(b)) for a, b in re.findall(r'(\d+),\s*(\d+)', txt))
SNAP = json.load(open(os.path.join(HERE, '..', 'data', 'remaining_before_q2_series.json')))

def isprime(p): return p > 1 and all(p % d for d in range(2, int(p ** 0.5) + 1))
def ordm(a, m):
    if m == 1: return 1
    k, x = 1, a % m
    while x != 1: x = x * a % m; k += 1
    return k

def thm_Q2(n, h):                         # n = 4q, q odd prime, h odd, q^2 does not divide h
    q = n // 4
    return n % 4 == 0 and q > 2 and isprime(q) and h % 2 == 1 and h % (q * q) != 0
def thm_Q2p(n, h):                        # Theorem Q2': n = 4q, q odd prime, h odd (no condition on v_q(h))
    q = n // 4
    return n % 4 == 0 and q > 2 and isprime(q) and h % 2 == 1
def W(q, h): return ordm(2, lcm(h, q * q)) != ordm(2, lcm(h, q))
def thm_E1(n, h):                         # n = 4q^2, q odd prime, h odd, q^2 does not divide h, condition (W)
    if n % 4: return False
    m = n // 4; q = int(round(m ** 0.5))
    return q * q == m and q > 2 and isprime(q) and h % 2 == 1 and h % m != 0 and W(q, h)
def selfconj2(M):                         # -1 in <2> inside (Z/M)^*
    x = 2 % M
    for _ in range(M + 1):
        if x == M - 1: return True
        x = x * 2 % M
        if x == 2 % M: break
    return False
def thm_E2(n, h):                         # n = 4qr, q < r odd primes, hypotheses of Theorem E2
    if n % 4 or h % 2 == 0: return False
    m = n // 4
    ps = [p for p in range(3, m + 1) if m % p == 0 and isprime(p)]
    if len(ps) != 2 or ps[0] * ps[1] != m: return False
    q, r = ps
    if vp(h, q) > 1 or vp(h, r) > 1 or m % 5 == 0: return False
    _, dq, dr = info(q, r, h)
    if not (dq and dr): return False
    return m % 3 != 0 or selfconj2(lcm(h, m)) or (m, h) == (21, 21)

THMS = [('Q2', thm_Q2), ("Q2'", lambda n, h: thm_Q2p(n, h) and not thm_Q2(n, h)), ('E1', thm_E1), ('E2', thm_E2)]
def closed_by(n, h): return [name for name, f in THMS if f(n, h)]

# 1. all Do Duc open entries covered by the four theorems (whatever earlier criteria say)
cov = sorted((n, h) for (n, h) in DODUC if closed_by(n, h))
print('Do Duc open entries satisfying the hypotheses of Q2/Q2\'/E1/E2: %d' % len(cov))
# 2. against the snapshot of entries not excluded by our earlier criteria
snap_open = [(e['n'], e['h']) for e in SNAP['entries'] if e['status'] == 'open']
snap_cond = [(e['n'], e['h']) for e in SNAP['entries'] if e['status'] != 'open']
assert len(snap_open) == SNAP['count_open'] == 81
new = [(n, h, closed_by(n, h)) for (n, h) in snap_open if closed_by(n, h)]
print('closed among the 81 snapshot entries: %d' % len(new))
for name, _ in THMS:
    print('  %-3s %s' % (name, [(n, h) for n, h, c in new if name in c]))
extra = [(28, 7)]   # in the Do Duc list; earlier excluded only by a GRH-conditional column computation
assert all(x in DODUC and closed_by(*x) and x not in snap_open for x in extra)
print('also closed unconditionally (previously GRH-conditional only): %s by %s' % (extra, [closed_by(*x) for x in extra]))
print('total newly closed entries: %d' % (len(new) + len(extra)))
print('snapshot entries conditional on (28,7), now covered directly: %s' % [(x, closed_by(*x)) for x in snap_cond])
assert all(closed_by(*x) for x in snap_cond)
# 3. remaining list
closed = set((n, h) for n, h, _ in new)
rem = [e for e in SNAP['entries'] if e['status'] == 'open' and (e['n'], e['h']) not in closed]
byq = {}
for e in rem:
    k = '+'.join(map(str, e['qs'])); byq[k] = byq.get(k, 0) + 1
print('remaining: %d, by q-set: %s' % (len(rem), byq))
out = ['{',
       ' "description": "Do Duc (2019) open pairs (n,h), n,h <= 100, with a cyclic Sylow-q subgroup of order q^2 and q not dividing h, that are not excluded by any criterion we implemented, after Theorems Q2, Q2\', E1, E2 of results/q2-series. Snapshot-relative: see results/q2-series/data/remaining_before_q2_series.json for the earlier (internal, unreleased) criteria. This is not a verified list of open cases. qs = primes q with nu_q(n) = 2 and q not dividing h.",',
       ' "generated_by": "results/q2-series/scripts/closed_entries.py",',
       ' "count": %d,' % len(rem),
       ' "count_by_q": %s,' % json.dumps(dict(sorted(byq.items()))),
       ' "entries": [']
out += ['  ' + json.dumps({'n': e['n'], 'h': e['h'], 'qs': e['qs']}) + (',' if i < len(rem) - 1 else '') for i, e in enumerate(rem)]
out += [' ]', '}']
open(os.path.join(ROOT, 'results', 'remaining-open-cases.json'), 'w').write('\n'.join(out) + '\n')
print('wrote results/remaining-open-cases.json')
