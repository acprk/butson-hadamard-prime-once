# Failure certificate for the two-term tau-descent at (n,h)=(60,15), q=3, r=5.
# Build X in O_K[C3], K=Q(zeta_60), with X X^* = 60 exactly, such that X(chi)/X(1) is NOT in k=Q(zeta_15).
# Then f = X (x) delta_{C5} in O_K[C3 x C5] has f f^* = 60, satisfies Lemma A at 3 and 5 and has Delta = 1 (Theorem P),
# but its two-term ratio is not in k.  Also checks the decomposition-group facts used in the report.
K.<z> = CyclotomicField(60)
i = z^15; w3 = z^20
k = K.subfield(z^4)[0]   # Q(zeta_15)
print("class number K:", K.class_number(proof=False))
R = K.primes_above(5); print("primes above 5:", len(R), [ (P.ramification_index(), P.residue_class_degree()) for P in R])
Q = K.primes_above(3); print("primes above 3:", len(Q), [ (P.ramification_index(), P.residue_class_degree()) for P in Q])
# tau: i -> -i, fixes zeta_15.  z = zeta_60; tau(z) = z^t with t = -1 mod 4, 1 mod 15 -> t = 31
tau = K.hom([z^31]); conj = K.hom([z^59])
print("tau(R0)==R0?", tau(R[0].gens_reduced()[0]) in R[0], " conj(R0)==R0?", conj(R[0].gens_reduced()[0]) in R[0])
pi = R[0].gens_reduced()[0]
w = pi/conj(pi)
print("w=pi/conj(pi): |w|=1 numerically:", abs(CC(w.complex_embedding()))  )
# sqrt(-15) in Q(zeta_15): Gauss sum
g15 = sum( kronecker(a,15)*z^(4*a) for a in range(1,15))
print("g15^2 =", g15^2)
g0 = 2*g15
def inK(x):
    try:
        return all(c in ZZ for c in K(x).list()) and K.ring_of_integers()(x) is not None
    except: return False
OK = K.ring_of_integers()
mu = [z^a for a in range(60)]
sols=[]
for j in range(-2,3):
    g = g0*w^j
    for m in range(-4,5):
        if m==0: continue
        if not (0 <= 2+j+m <= 4): continue
        for m2 in range(-4,5):
            if not (0 <= 2+j+m2 <= 4): continue
            for a in range(60):
                u = w^m*mu[a]
                for b in range(60):
                    u2 = w^m2*mu[b]
                    F = [g, g*u, g*u2]   # X(1), X(chi), X(chibar), chi(1)=w3
                    xs = [ (F[0] + F[1]*w3^(-t) + F[2]*w3^(t))/3 for t in range(3)]
                    if all(x.is_integral() for x in xs):
                        sols.append((j,m,m2,a,b,xs))
                        break
                if sols and sols[-1][:4]==(j,m,m2,a): break
    if len(sols)>=3: break
print("found", len(sols))
for (j,m,m2,a,b,xs) in sols[:3]:
    X = xs
    # verify X X^* = 60 in K[C3]: coefficient c_t = sum_s x_s conj(x_{s-t})
    c = [ sum(X[s]*conj(X[(s-t)%3]) for s in range(3)) for t in range(3)]
    r = (X[0]+X[1]*w3+X[2]*w3^2)/(X[0]+X[1]+X[2])
    print("j,m,m2,a,b=",(j,m,m2,a,b)," XX* coeffs:", c, " ratio in k?", tau(r)==r, " v_R0(X(1)),v_R0(X(chi)):",
          (X[0]+X[1]+X[2]).valuation(R[0]), (X[0]+X[1]*w3+X[2]*w3^2).valuation(R[0]),
          " eps=tau(r)/r root of unity?", ("root of unity" if (tau(r)/r)^120==1 else "NOT a root of unity"))
    print("   coefficients x_0,x_1,x_2 =", X)
    print("   max |x_t| over embeddings:", [max(abs(e) for e in x.complex_embeddings()) for x in X])
