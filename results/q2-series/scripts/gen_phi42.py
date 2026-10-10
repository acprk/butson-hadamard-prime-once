# Regenerates phi42.h: row a = coefficients of x^a mod Phi_42(x) in the power basis 1, x, ..., x^11.
# wexact.c uses it to test exactly whether a sum of 42nd roots of unity vanishes.
# usage: python3 gen_phi42.py > phi42.h
def polymul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): r[i + j] += x * y
    return r
def polydiv_exact(a, b):          # a / b, b monic, exact division
    a = a[:]; q = [0] * (len(a) - len(b) + 1)
    for i in range(len(q) - 1, -1, -1):
        q[i] = a[i + len(b) - 1]
        for j, y in enumerate(b): a[i + j] -= q[i] * y
    assert all(c == 0 for c in a)
    return q
def cyclo(n, memo={}):
    if n in memo: return memo[n]
    p = [-1] + [0] * (n - 1) + [1]  # x^n - 1
    for d in range(1, n):
        if n % d == 0: p = polydiv_exact(p, cyclo(d))
    memo[n] = p; return p
P = cyclo(42); D = len(P) - 1
rows = []
cur = [1] + [0] * (D - 1)
for a in range(42):
    rows.append(cur)
    nxt = [0] + cur              # multiply by x
    lead = nxt[D]
    cur = [nxt[i] - lead * P[i] for i in range(D)]
print('#define DEG %d' % D)
print('static const int RED[42][%d]={%s};' % (D, ','.join('{' + ','.join(map(str, r)) + '}' for r in rows)))
