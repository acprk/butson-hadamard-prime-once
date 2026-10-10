# Where do the real h-even controls escape Theorem E1?  (q=3: Z36,h=6; q=5: Z100,h=10)
import numpy as np, random, itertools
from collections import Counter
def run(q,h,trials,seed):
    random.seed(seed); m=q*q; n=4*m; r_=int(round(n**0.5)); zq=np.exp(2j*np.pi/q)
    st=Counter()
    for _ in range(trials):
        pi=list(range(r_)); random.shuffle(pi); psi=[random.randrange(h) for _ in range(r_)]
        x=np.array([np.exp(2j*np.pi*((pi[k]*j*(h//r_) + psi[k])%h)/h) for mm in range(n) for (j,k) in [divmod(mm,r_)]])
        C=np.zeros((4,m),complex)
        for g in range(n): C[g%4][g%m]=x[g]
        Dp=np.array([[sum(C[y][(r+q*t)%m] for t in range(q)) for r in range(q)] for y in range(4)])
        nzc=[r for r in range(q) if np.abs(Dp[:,r]).max()>1e-8]
        if len(nzc)==1:
            X=Dp[:,nzc[0]]/q
            st[('one class: X in mu_h and BH(C4,h)', bool(np.allclose(np.abs(X),1) and np.allclose(np.abs(np.fft.fft(X))**2,4)))]+=1
        else:
            for r in nzc:
                U=Dp[:,r]
                if np.allclose(U[2],-U[0]) and np.allclose(U[3],-U[1]):
                    # {1,3}-class: fibres constant with x_{y+2} = -x_y ?
                    ok=all(np.allclose(C[y][[(r+q*t)%m for t in range(q)]], -C[(y+2)%4][[(r+q*t)%m for t in range(q)]]) for y in range(4) if abs(U[y])>1e-8)
                    st[('two classes: {1,3}-class uses x_{y+2}=-x_y', ok)]+=1
    return st
print("q=3,h=6 :", dict(run(3,6,2000,11)))
print("q=5,h=10:", dict(run(5,10,800,12)))
