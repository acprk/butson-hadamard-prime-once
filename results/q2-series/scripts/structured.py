# Structured search for BH(C4 x C_q, h), h odd, using ONLY Steps 1-3,5 (see ../theorem-q2.md):
#   a = C0-C2 = kappa*b, b = C1-C3, kappa in k real, nonzero, b != 0.
# No Lemma K, no column law, no Sigma4 classification, no Galois averaging is assumed:
#   classes are computed numerically from all h^4 column types; the identity-coefficient identity
#   sum_{w in S} (|a_w|^2+|b_w|^2) = 4q is imposed at EVERY embedding (it is an identity in Q), then every surviving
#   configuration is completed by brute force over off-support columns (u,v,u,v) and checked for perfectness.
import sys, math, itertools, numpy as np
from collections import defaultdict
q, h = int(sys.argv[1]), int(sys.argv[2])
embs = [j for j in range(1, h) if math.gcd(j, h) == 1]
Z = np.exp(2j*np.pi*np.outer(np.arange(h), embs)/h)            # Z[e, emb]
X = np.array(list(itertools.product(range(h), repeat=4)))      # (x0,x1,x2,x3)
x0,x1,x2,x3 = X.T
S = (x0 != x2) & (x1 != x3)
X = X[S]; x0,x1,x2,x3 = X.T
a = Z[x0,0]-Z[x2,0]; b = Z[x1,0]-Z[x3,0]; kap = a/b
real = np.abs(kap.imag) < 1e-9
print('S-type columns %d, with real kappa %d  (column law x0+x2=x1+x3 holds for all real-kappa types: %s)' %
      (len(X), real.sum(), bool(np.all(((x0+x2-x1-x3) % h)[real] == 0))))
X = X[real]; kr = kap.real[real]
o = np.argsort(kr); X = X[o]; kr = kr[o]
classes = []; st = 0
for i in range(1, len(kr)+1):
    if i == len(kr) or kr[i]-kr[i-1] > 1e-9*max(1,abs(kr[i])): classes.append((st, i)); st = i
if len(sys.argv)>3 and sys.argv[3]=='withzero':   # CONTROL ONLY: add the kappa=0 class (a=0, b!=0), excluded for h odd by Step 4
    Z0=np.array([c for c in itertools.product(range(h),repeat=4) if c[0]==c[2] and c[1]!=c[3]])
    classes.append((len(X),len(X)+len(Z0))); X=np.vstack([X,Z0]); kr=np.concatenate([kr,np.zeros(len(Z0))])
print('kappa classes:', len(classes), ' sizes histogram:', dict(sorted(defaultdict(int, {}).items())))
sizes = defaultdict(int)
for s_, e_ in classes: sizes[e_-s_] += 1
print('  class-size histogram:', dict(sorted(sizes.items())))

# three identity-coefficient filters, each an identity in Q hence imposed at every embedding:
#   sum_S |a|^2+|b|^2 = 4q,   sum_all |e_+|^2 = 4q,   sum_all |e_-|^2 = 4q   (e_+- = C0+C2 +- (C1+C3))
def feats(cols):
    A=Z[cols[:,0]]; B=Z[cols[:,1]]; C=Z[cols[:,2]]; D_=Z[cols[:,3]]
    return np.hstack([np.abs(A-C)**2+np.abs(B-D_)**2, np.abs(A+C+B+D_)**2, np.abs(A+C-B-D_)**2])
ne=len(embs)
offcols=np.array([(u,v,u,v) for u in range(h) for v in range(h)])
offF=feats(offcols)[:,ne:]
offkey={}
for r,row in enumerate(np.round(offF,7)): offkey.setdefault(tuple(row),[]).append(r)
offtypes=list(offkey); OT=np.array(offtypes)
surv=[]
for ci,(s_,e_) in enumerate(classes):
    cols=X[s_:e_]; F=feats(cols)
    keyd={}
    for r,row in enumerate(np.round(F,7)): keyd.setdefault(tuple(row),[]).append(r)
    types=list(keyd); T=np.array(types)
    for s in range(1,q+1):
        for combo in itertools.combinations_with_replacement(range(len(types)),s):
            v=T[list(combo)].sum(axis=0)
            if not np.all(np.abs(v[:ne]-4*q)<1e-6): continue
            res=4*q-v[ne:]
            for oc in itertools.combinations_with_replacement(range(len(offtypes)),q-s):
                w=OT[list(oc)].sum(axis=0) if oc else np.zeros(2*ne)
                if np.all(np.abs(w-res)<1e-6): surv.append((ci,kr[s_],cols,keyd,types,combo,oc))
print('(class, S-multiset, off-multiset) configurations surviving the three identity filters:',len(surv))
def perfect(D):
    n=4*q; xs=np.array([D[g%q][g%4] for g in range(n)])
    for j in embs:
        for sh in range(1,n):
            if abs(np.sum(np.exp(2j*np.pi*j*((np.roll(xs,-sh)-xs)%h)/h)))>1e-7: return False
    return True
z0=Z[:,0]; total=0; hits=0
for ci,kv,cols,keyd,types,combo,oc in surv:
    s=len(combo); print('  survivor: kappa=%.6f |S|=%d S-types %s off-types %s'%(kv,s,combo,oc),flush=True)
    for Spos in itertools.combinations(range(1,q),s-1):
        Spos=(0,)+Spos; off=[w for w in range(q) if w not in Spos]
        for perm in set(itertools.permutations(combo)):
            pools=[keyd[types[t]] for t in perm]
            # global scalar: first S column normalised to x0=0
            pools[0]=[r for r in pools[0] if cols[r][0]==0]
            for choice in itertools.product(*pools):
                bv=np.zeros(q,complex)
                for w,r in zip(Spos,choice): c=cols[r]; bv[w]=z0[c[1]]-z0[c[3]]
                fb=np.abs(np.fft.fft(bv))**2
                if fb.max()-fb.min()>1e-6: continue
                for operm in set(itertools.permutations(oc)):
                    opools=[offkey[offtypes[t]] for t in operm]
                    for ochoice in itertools.product(*opools):
                        D=[None]*q
                        for w,r in zip(Spos,choice): D[w]=tuple(cols[r])
                        for w,r in zip(off,ochoice): D[w]=tuple(offcols[r])
                        total+=1
                        if perfect(D): hits+=1; print('    HIT',D,flush=True)
print('q=%d h=%d: full configurations checked %d, perfect hits %d'%(q,h,total,hits))
