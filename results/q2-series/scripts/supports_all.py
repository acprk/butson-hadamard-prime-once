# all 7-subsets of Z21 containing 0 with no nonzero difference represented exactly once (NO multiplier reduction)
import itertools
n,k=21,7
for rest in itertools.combinations(range(1,n),k-1):
    T=(0,)+rest; cnt=[0]*n
    for x in T:
        for y in T:
            if x!=y: cnt[(x-y)%n]+=1
    if 1 in cnt: continue
    print(' '.join(map(str,T)))
