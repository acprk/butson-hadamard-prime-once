import re,sys
sys.path.insert(0,'../ramified')
from math import gcd,isqrt
from fdesc import fac,selfconj,order,m_q
from ramified_new import duc37
txt=open('DoDuc_BH_open_cases.txt').read()
L={(int(a),int(b)) for a,b in re.findall(r'(\d+)\s*,\s*(\d+)',txt)}
def isprime(x): return x>1 and all(x%d for d in range(2,isqrt(x)+1))
def lcm(a,b): return a*b//gcd(a,b)
def v(p,x):
    k=0
    while x%p==0: x//=p;k+=1
    return k
def lamleung(n,h):
    ps=list(fac(h)) if h>1 else []
    ok=[False]*(n+1);ok[0]=True
    for i in range(1,n+1):
        ok[i]=any(i>=p and ok[i-p] for p in ps)
    return ok[n]
def excl1(n,h):
    # Result 1.1
    for p in range(3,n):
        if isprime(p) and n==2*p*p and h==2*p: return '1.1.1'
    f=fac(n)
    if h==3 and n%3==0:
        r=n//3
        ff=fac(r)
        if len(ff)==2 and all(e==1 for e in ff.values()) and all(x>3 for x in ff): return '1.1.2'
    fh=fac(h)
    if len(fh)==2 and all(e==1 for e in fh.values()) and all(x>3 for x in fh) and n==sum(fh): return '1.1.3'
    # 1.2
    if h==2 and not (n==1 or n==2 or n%4==0): return '1.2i'
    if h==2 and n%4==0 and isqrt(n//4)**2!=n//4: return '1.2i'
    if h==2 and n==2: pass
    if isprime(n-2) and n-2>=3:
        p=n-2
        if h%2==0 and h>2 and set(fac(h//2))=={p}: return '1.2ii'
    if n%2==0 and isprime(n//2) and n//2>=3:
        q=n//2
        if h%2==0:
            r=h
            while r%2==0:r//=2
            fr=fac(r)
            if len(fr)==1 and list(fr)[0]>q: return '1.2iii'
    if not lamleung(n,h): return '1.3'
    m=1
    for p,e in f.items():
        if e%2:m*=p
    if m%2==1:
        for p in fac(m):
            if h%p and any(pow(p,j,h)==(h-1)%h for j in range(1,2*h+2)): return '1.4'
    return None
def exist15(n,h):
    for p,e in fac(n).items():
        if v(p,h)<(e+1)//2: return False
    if v(2,n)==1 and v(2,h)<2: return False
    return True
def t32(n,h):
    m=lcm(n,h);f=fac(n)
    for p in f:
        if h%p: return None
        for q in f:
            if q!=p and pow(q,order(q,m_q(m,q)),p**(v(p,h)+1))==1: return None
    return 'T3.2' if n>gcd(h,n)**2 else None
def t33(n,h):
    m=lcm(n,h)
    return 'T3.3' if any(h%p and selfconj(p,m) for p in fac(n)) else None
def t311(n,h):
    fh=fac(h)
    odd=[p for p in fh if p>2]
    if len(odd)!=1: return None
    p=odd[0]
    if not (h==p**fh[p] or h==2*p**fh[p]): return None
    c=v(p,n);mm=n//p**c
    if isqrt(mm)**2==mm: return None
    qs=list(fac(mm));f=0
    for q in qs: f=gcd(f,order(q,p))
    if f%2==0: return 'T3.11i'
    from fractions import Fraction
    if not (f<=mm or p<=Fraction(f*f-mm,f-mm)): return 'T3.11ii'
    if p>mm*mm+mm+1: return 'T3.11iii'
    return None
open1=[];open2=[];final=set()
for n in range(1,101):
  for h in range(1,101):
    if excl1(n,h): continue
    open1.append((n,h))
    if exist15(n,h) or len(fac(n))<=1: continue
    open2.append((n,h))
    if t32(n,h) or t33(n,h) or duc37(n,h) or t311(n,h): continue
    final.add((n,h))
print(len(open1),len(open2),len(final),len(L))
print('in recon not in list',sorted(final-L)[:50], len(final-L))
print('in list not in recon',sorted(L-final)[:50], len(L-final))
# closure: (n,h) excluded if (n,kh) excluded by explicit criteria for some kh<=100
def explicit_excl(n,h):
    if excl1(n,h): return True
    if exist15(n,h) or len(fac(n))<=1: return False
    return bool(t32(n,h) or t33(n,h) or duc37(n,h) or t311(n,h))
final2=set(x for x in final if not any(explicit_excl(x[0],k*x[1]) for k in range(2,100//x[1]+1)))
print('closure', len(final2), sorted(final2-L), sorted(L-final2))
for x in sorted(final-L):
    print(x,[ (k*x[1]) for k in range(2,100//x[1]+1) if explicit_excl(x[0],k*x[1])][:5])
print('h=3 in list:',sorted(n for n,h in L if h==3))
print('h=3 recon:',sorted(n for n,h in final if h==3))
print('h=7 list', sorted(n for n,h in L if h==7)); print('h=7 recon',sorted(n for n,h in final if h==7))
print('54 list', sorted(h for n,h in L if n==54))
print('54 recon', sorted(h for n,h in final if n==54))
