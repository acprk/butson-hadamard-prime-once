# entries (n=4qr,h) closed by Theorem E2 (conditions as in ../theorem-e2.md)
from decomp import info, vp, lcm
def selfconj2(M):
    x=2%M
    for _ in range(M+1):
        if x==M-1: return True
        x=x*2%M
        if x==2%M: break
    return False
P=[p for p in range(3,250) if all(p%d for d in range(2,p))]
res=[]; res_core=[]
for a,q in enumerate(P):
    for r in P[a+1:]:
        m=q*r; n=4*m
        if n>1000: continue
        for h in range(3,301,2):
            if vp(h,q)>1 or vp(h,r)>1: continue
            if m%5==0: continue
            out,dq,dr=info(q,r,h)
            if not(dq and dr): continue
            M=lcm(h,m)
            if m%3==0 and not selfconj2(M) and (m,h)!=(21,21): continue
            res.append((n,h))
            if h%q==0 and h%r==0: res_core.append((n,h))
print(len(res), "entries with n<=1000,h<=300;", len(res_core), "with qr|h")
print("qr|h:", res_core)
print("n<=100:", [x for x in res if x[0]<=100])
