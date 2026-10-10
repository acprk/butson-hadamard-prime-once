# Controls: generalized Frank sequences of length 36 = 6^2 over mu_h (h = 6, 18), cyclic Z36 = C4 x C9.
# a(6j+k) = zeta_6^{pi(k) j} * psi(k)   (perfect for any permutation pi of Z6 and phases psi)
# For each object compute Q2 steps: a = C0-C2, b = C1-C3 on C9; one kappa? kappa real? column law?
import numpy as np, itertools, random, sys
from collections import Counter
random.seed(1)
def perfect(x):
    F = np.fft.fft(x); return np.allclose(np.abs(F)**2, len(x))
def analyse(x):
    n=len(x); C=np.zeros((4,9),complex)
    for g in range(n): C[g%4][g%9]=x[g]
    a=C[0]-C[2]; b=C[1]-C[3]
    S=[w for w in range(9) if abs(a[w])>1e-9 or abs(b[w])>1e-9]
    ks=[]
    for w in S:
        ks.append(np.inf if abs(b[w])<1e-9 else a[w]/b[w])
    distinct=[]
    for k in ks:
        if not any((k==np.inf and d==np.inf) or (k!=np.inf and d!=np.inf and abs(k-d)<1e-7) for d in distinct): distinct.append(k)
    real=all(k==np.inf or abs(k.imag)<1e-7 for k in distinct)
    # rho_chi = f(chi)/tau f(chi) for chi of C9: f = a+ib, tauf = a-ib
    f=a+1j*b; tf=a-1j*b
    Ff=np.fft.fft(f); Ft=np.fft.fft(tf)
    # NB numeric tau at one embedding is fine because a,b have coefficients in Q(zeta_h), h=6/18 not containing i
    rho=[Ff[c]/Ft[c] if abs(Ft[c])>1e-9 else None for c in range(9)]
    rhoconst = all(r is not None and abs(r-rho[0])<1e-7 for r in rho)
    return len(distinct), real, len(S), rhoconst
for h in (6,18):
    st=Counter(); tot=0
    perms=list(itertools.permutations(range(6)))
    for trial in range(4000):
        pi=random.choice(perms); psi=[random.randrange(h) for _ in range(6)]
        x=np.array([np.exp(2j*np.pi*((h//6)*pi[k]*j + psi[k])/h) for m in range(36) for (j,k) in [divmod(m,6)]])
        assert perfect(x)
        st[analyse(x)]+=1
    print("h=%d generalized Frank, 4000 random: (#kappa, kappa real, |S|, rho const):"%h, dict(st))
