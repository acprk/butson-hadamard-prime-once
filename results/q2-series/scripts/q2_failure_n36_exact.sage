# Exact analysis of failing h=6 generalized-Frank BH(Z36,6): q-valuations of f(chi), eps = tau(r)/r
import itertools, random
random.seed(int(1))
L.<z> = CyclotomicField(36)   # contains i = z^9, zeta_6 = z^6, zeta_9 = z^4
I_ = z^9; z6 = z^6; z9 = z^4
tau = L.hom([z^19])   # 19 = -1 mod 4, 1 mod 9
assert tau(I_) == -I_ and tau(z9) == z9 and tau(z6) == z6
P3 = L.primes_above(3); P2 = L.primes_above(2)
print("#primes above 3:", len(P3), " above 2:", len(P2), " tau fixes 3-primes?", [P3.index(tau(P)) for P in P3])
def obj(pi, psi):
    return [z6^((pi[k]*j + psi[k]) % 6) for m in range(36) for (j,k) in [divmod(m,6)]]
perms = list(itertools.permutations(range(6)))
shown = 0
# with this seed the first failing object is pi=(1,0,4,5,3,2), psi=(4,0,2,0,3,3), quoted in the documentation
for trial in range(400):
    pi = random.choice(perms); psi = [random.randrange(6) for _ in range(6)]
    x = obj(pi, psi)
    C = [[x[g] for g in range(36) if g % 4 == y] for y in range(4)]
    Cw = [[None]*9 for _ in range(4)]
    for g in range(36): Cw[g % 4][g % 9] = x[g]
    a = [Cw[0][w]-Cw[2][w] for w in range(9)]; b = [Cw[1][w]-Cw[3][w] for w in range(9)]
    f = [a[w]+I_*b[w] for w in range(9)]
    fv = [sum(f[w]*z9^(c*w) for w in range(9)) for c in range(9)]
    rho = [fv[c]/tau(fv[c]) for c in range(9)]
    if all(r == rho[0] for r in rho): continue
    vals = [[fv[c].valuation(P) for P in P3] for c in range(9)]
    r = [fv[c]/fv[0] for c in range(9)]
    eps = [tau(r[c])/r[c] for c in range(9)]
    epsv = [[e.valuation(P) for P in P3] for e in eps]
    print("pi,psi", pi, psi)
    print("  v_Q(f(chi)) per chi (Q above 3):", vals)
    print("  eps unit at 3-primes per chi:", [all(v == 0 for v in ev) for ev in epsv])
    print("  eps root of unity?:", [e.multiplicative_order() if all(v==0 for v in ev) else None for e,ev in zip(eps,epsv)])
    shown += 1
    if shown >= 4: break
