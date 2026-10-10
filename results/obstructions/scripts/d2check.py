"""Theorem D2 check: relabel Do Duc's BH(C_q x C_q, h) (exists) to G = C_{q^2} via beta(i + q j) = (i, j).
Verify that the relabelled matrix M satisfies every constraint listed in Theorem D2 for G (BH rows/cols, row-quotient product 1 on
every <s-t>_G coset, G/C_q projection group-invariant), while M is NOT G-invariant.  q=5,h=6 (BH(Z_25,6) is known not to exist)."""
import itertools, cmath, math
q,h=5,6
etas=[0,3,1,3,5]   # exponents (mod 6) of a vanishing sum of q sixth roots: 1 + (-1) + zeta6 + (-1)... check below
z=lambda k: cmath.exp(2j*math.pi*k/h)
assert abs(sum(z(e) for e in etas))<1e-12
def D(x,y):  # Do Duc: D_i = {(x,y): x!=0, y/x=i} u ({0}xF_q if i=0); value eta_i on D_i
    i=(y*pow(x,-1,q))%q if x%q else 0
    return etas[i]
# verify perfect on C_q x C_q
G2=[(x,y) for x in range(q) for y in range(q)]
for s in G2:
    if s==(0,0): continue
    assert abs(sum(z(D((a+s[0])%q,(b+s[1])%q)-D(a,b)) for a,b in G2))<1e-9
n=q*q
beta=lambda x: (x%q, x//q)
M=[[D((beta(y)[0]+beta(s)[0])%q,(beta(y)[1]+beta(s)[1])%q) for y in range(n)] for s in range(n)]
# (1) BH
ok1=all(abs(sum(z(M[s][y]-M[t][y]) for y in range(n)))<1e-9 for s in range(n) for t in range(n) if s!=t)
# (2) product 1 on <s-t> cosets of Z_25
ok2=True
for s in range(n):
    for t in range(n):
        if s==t: continue
        w=(s-t)%n; o=n//math.gcd(w,n); sub=[(k*w)%n for k in range(o)]
        for c in range(n):
            if sum((M[s][(c+k)%n]-M[t][(c+k)%n]) for k in sub)%h: ok2=False
# (3) not G-invariant
ok3=any(M[(s+1)%n][y]!=M[s][(y+1)%n] for s in range(n) for y in range(n))
# (4) projection to G/C_q (C_q = 5Z_25): P[s][c] = sum_{y = c mod 5} zeta^M[s][y] depends only on (c+s) mod 5
P=lambda s,c: sum(z(M[s][y]) for y in range(n) if y%q==c)
ok4=all(abs(P(s,c)-P(0,(c+s)%q))<1e-9 for s in range(n) for c in range(q))
# (5) is it perfect as a C_25 sequence? (row 0 autocorrelation)
r0=[M[0][y] for y in range(n)]
ac=max(abs(sum(z(r0[(y+u)%n]-r0[y]) for y in range(n))) for u in range(1,n))
print('BH:',ok1,' coset-products=1 for all row pairs:',ok2,' NOT G-invariant:',ok3,' G/C_q projection group-invariant:',ok4,' max |autocorr| of row0 on C_25: %.3f'%ac)
