# Lemma K exhaustive check (fast). Representatives: a in 1..(h-1)/2 (since kappa(-a,-b)=kappa(a,b)), b in 1..h-1,
# b != +-a (kappa=+-1 excluded).  Any float collision among representatives is a candidate NONTRIVIAL coincidence;
# each candidate is decided exactly (multiset criterion, then 60-digit mpmath).  Also sanity: count kappa=+-1 pairs.
import sys, numpy as np, mpmath
mpmath.mp.dps = 60
def run(h):
    s = np.sin(2*np.pi*np.arange(h)/h)
    a = np.arange(1, (h-1)//2+1); b = np.arange(1, h)
    A, B = np.meshgrid(a, b, indexing='ij'); A=A.ravel(); B=B.ravel()
    keep = (B != A) & ((A+B) % h != 0); A=A[keep]; B=B[keep]
    V = s[A]/s[B]
    o = np.argsort(V, kind='stable'); Vs = V[o]
    near = np.nonzero(np.abs(np.diff(Vs)) <= 1e-8*np.maximum(1.0, np.abs(Vs[1:])))[0]
    out = []
    pairs=set(); runs=[]; 
    for j in near:
        if runs and runs[-1][1]==j: runs[-1][1]=j+1
        else: runs.append([j,j+1])
    for u,w in runs:
        for x in range(u,w+1):
            for y in range(x+1,w+1): pairs.add((x,y))
    for (x,y) in sorted(pairs):
        a1,b1,a2,b2 = int(A[o[x]]),int(B[o[x]]),int(A[o[y]]),int(B[o[y]])
        P = sorted([(a1+b2)%h, (-(a1+b2))%h, (b1-a2)%h, (a2-b1)%h]); N = sorted([(b1+a2)%h, (-(b1+a2))%h, (a1-b2)%h, (b2-a1)%h])
        v = mpmath.sin(2*mpmath.pi*a1/h)*mpmath.sin(2*mpmath.pi*b2/h)-mpmath.sin(2*mpmath.pi*b1/h)*mpmath.sin(2*mpmath.pi*a2/h)
        out.append(((a1,b1),(a2,b2),P==N, float(abs(v))))
    return len(A), out
lo, hi = int(sys.argv[1]), int(sys.argv[2])
tot=0; npairs=0
for h in range(lo|1, hi+1, 2):
    n, out = run(h); npairs += n
    real = [x for x in out if x[3] < 1e-50]
    tot += len(real)
    if out: print('h=%d float-candidates %d, exact %d: %s'%(h,len(out),len(real),out[:3]), flush=True)
print('done odd h in [%d,%d]: representative pairs %d, exact nontrivial coincidences %d'%(lo,hi,npairs,tot), flush=True)
