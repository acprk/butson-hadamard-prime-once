import itertools, cmath, sys
sys.setrecursionlimit(10000)
def count(n,h,limit=None):
    w=[cmath.exp(2j*cmath.pi*k/h) for k in range(h)]
    c=0
    for t in itertools.product(range(h),repeat=n-1):
        a=(0,)+t
        ok=True
        for s in range(1,n):
            z=sum(w[a[(x+s)%n]]*w[a[x]].conjugate() for x in range(n))
            if abs(z)>1e-9: ok=False;break
        if ok:c+=1
    return c
print("predict 0 (n≡2 mod 4, h≡2 mod 4):")
for n,h in [(2,2),(2,6),(2,10),(6,6),(6,2),(10,2),(2,14),(6,10)]:
    print(n,h,count(n,h),flush=True)
print("controls (4|h):")
for n,h in [(2,4),(2,8),(6,12),(2,12)]:
    print(n,h,count(n,h),flush=True)
