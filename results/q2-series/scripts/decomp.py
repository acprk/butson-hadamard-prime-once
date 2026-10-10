# Decomposition-group test for the two tau-descent directions on C4 x C_q x C_r, h odd.
# K = Q(zeta_L), L = 4*lcm(h,q,r). Gal = (Z/L)^*.  tau = (-1 mod 4, 1 mod L/4), c = -1.
# dir_q (two-term ratio in the q-direction lies in k) needs: v_q(h)<=1 (Lemma A at q) and, at primes over r,
#   tau in D_r or c in D_r   (tau-fixed, or self-conjugate => v_R(F) = v_R(4qr)/2 for every character value).
from math import gcd
def lcm(a,b): return a*b//gcd(a,b)
def vp(n,p):
    k=0
    while n%p==0: n//=p; k+=1
    return k
def crt(a,m,b,n):
    for x in range(a, m*n, m):
        if x%n==b%n: return x
def inD(t,p,L):
    pa=p**vp(L,p); Lp=L//pa
    t%=Lp
    x=1
    for _ in range(Lp+1):
        if x%Lp==t: return True
        x=x*p%Lp
    return False
def info(q,r,h):
    L=4*lcm(lcm(h,q),r)
    tau=crt(3,4,1,L//4); c=L-1
    out={}
    for p,o in ((q,r),(r,q)):
        out[p]=dict(tau=inD(tau,p,L),c=inD(c,p,L),ctau=inD(tau*c%L,p,L),vh=vp(h,p))
    dq = out[q]['vh']<=1 and (out[r]['tau'] or out[r]['c'])
    dr = out[r]['vh']<=1 and (out[q]['tau'] or out[q]['c'])
    return out,dq,dr
if __name__=='__main__':
    import sys
    for (q,r,h) in [(3,5,15),(3,5,45),(3,5,75),(3,7,21),(3,7,63)]:
        out,dq,dr=info(q,r,h)
        print((4*q*r,h),'q=%d r=%d'%(q,r),out,'dir_q',dq,'dir_r',dr)
    # survey: all 4qr<=1000, h odd <= 300 with q,r | h (Do Duc range where q,r|h is the hard case)
    from collections import Counter
    C=Counter(); ex={}
    P=[p for p in range(3,60) if all(p%d for d in range(2,p))]
    for i,q in enumerate(P):
        for r in P[i+1:]:
            for h in range(q*r, 400, 2):
                if h%q or h%r: continue
                out,dq,dr=info(q,r,h)
                key=(dq,dr); C[key]+=1; ex.setdefault(key,[]).append((4*q*r,h))
    print(C)
    for k,v in ex.items(): print(k, v[:12])
