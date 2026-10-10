# supports T of size k in Z_n where no nonzero difference occurs exactly once (necessary for weighing BB*=k over roots of unity:
# a vanishing sum of roots of unity cannot have exactly one term)
import itertools, sys
n=int(sys.argv[1]); k=int(sys.argv[2])
units=[u for u in range(1,n) if __import__('math').gcd(u,n)==1]
seen=set(); reps=[]
for rest in itertools.combinations(range(1,n),k-1):
    T=(0,)+rest
    cnt=[0]*n
    for x in T:
        for y in T:
            if x!=y: cnt[(x-y)%n]+=1
    if 1 in cnt: continue
    # canonical form under translation and multiplication by units
    best=None
    for u in units:
        for t in T:
            c=tuple(sorted(((x-t)*u)%n for x in T))
            if best is None or c<best: best=c
    if best in seen: continue
    seen.add(best); reps.append(best)
print(len(reps))
for r in reps: print(r)
