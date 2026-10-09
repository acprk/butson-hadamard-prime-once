import itertools, cmath
def count(n,h):
    w=[cmath.exp(2j*cmath.pi*k/h) for k in range(h)]
    c=0
    for t in itertools.product(range(h),repeat=n-1):
        a=(0,)+t   # normalize a0=1
        ok=True
        for s in range(1,n):
            z=sum(w[a[(x+s)%n]]*w[a[x]].conjugate() for x in range(n))
            if abs(z)>1e-9: ok=False;break
        if ok:c+=1
    return c
# S predicts 0: (n,h) with prime p||n, p∤h
for n,h in [(6,4),(10,4),(6,8),(3,2),(6,5),(5,4),(12,4)]:
    print("S-predicts-0",n,h,count(n,h))
# positive controls (not covered by S)
for n,h in [(4,4),(4,2),(9,3),(5,5),(2,4),(8,4)]:
    print("control",n,h,count(n,h))
