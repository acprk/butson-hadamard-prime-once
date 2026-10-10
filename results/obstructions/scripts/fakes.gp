\\ "Fake" perfect elements D in Z[zeta_h][C_{q^2} x C_m] with D D^* = q^2 m exactly
\\ (integral, Galois-compatible automatically) whose order-q^2 character values are NOT divisible by q.
\\ Shows: ideal structure + Galois + Fourier integrality cannot force q | chi(D); only coefficient unimodularity can.
\\ Run:  gp -q fakes.gp
default(parisize, 10^8);

\\ ---------- group ring helpers: D is a q2 x m matrix of polmods in t (= zeta_h) ----------
cnj(a, h) = { my(p = lift(a)); Mod(substpol(p, t, 0) + sum(k=1, poldegree(p), polcoeff(p,k,t)*t^(h-k)), polcyclo(h,t)); }
\\ exact check of D D^* = n * [0]
isperfect(D, h) = {
  my(Q = #D[,1], M = #D[1,], C = matrix(Q, M, i, j, cnj(D[i,j], h)), n = Q*M, s);
  for (s1 = 0, Q-1, for (s2 = 0, M-1,
    s = sum(y = 0, Q-1, sum(x = 0, M-1, D[y+1, x+1] * C[((y - s1) % Q) + 1, ((x - s2) % M) + 1]));
    if (s != if (s1 == 0 && s2 == 0, n, 0), return(0))));
  1;
}
\\ character value chi_{(k,l)}(D) in Q(zeta_N), returned as polmod in z = zeta_N
chival(D, h, N, k, l) = {
  my(Q = #D[,1], M = #D[1,], P = polcyclo(N, z), r = 0);
  for (y = 0, Q-1, for (x = 0, M-1,
    r += subst(lift(D[y+1, x+1]), t, z^(N/h)) * z^((N/Q)*k*y + (N/M)*l*x)));
  Mod(r, P);
}
\\ q | w in Z[zeta_N]  <=> all power-basis coefficients divisible by q (power basis is integral)
qdiv(w, q) = { my(p = lift(w)); for (i = 0, poldegree(p), if (polcoeff(p, i) % q, return(0))); 1; }

\\ Chu / Frank perfect sequences over mu_m (m odd) or the length-4 binary one; lifted to Z[zeta_h]
chu(m, h) = { if (m == 4, return([1,1,1,-1]*Mod(1,polcyclo(h,t))));
  if (m % 2 == 0, return(vector(m, j, Mod(t^((h/(2*m)) * ((j-1)^2 % (2*m))), polcyclo(h,t)))));
  if (m == 2, return([1, Mod(t^(h/4), polcyclo(h,t))]));   \\ (1, i): BH(C2,4), needs 4|h
  vector(m, j, Mod(t^((h/m) * (((j-1)*j/2) % m)), polcyclo(h,t))); }

report(name, D, h, q, N) = {
  my(Q = #D[,1], M = #D[1,], bad = 0, tot = 0);
  print("== ", name, ":  |G| = ", Q*M, "  h = ", h, "  q = ", q);
  print("   D D^* = |G| exactly : ", isperfect(D, h));
  for (k = 0, Q-1, if (gcd(k, Q) == 1, for (l = 0, M-1, tot++;
    if (!qdiv(chival(D, h, N, k, l), q), bad++))));
  print("   order-q^2 characters with q NOT dividing chi(D): ", bad, " / ", tot);
}

\\ ---------- (72,8): Gauss-type fake, q=3, F_9 = F_3[i], omega of order 8 ----------
{
  h = 8; q = 3; T8 = Mod(t, polcyclo(8, t));
  \\ F_9 elements a+b*i, generator 1+i ; enumerate powers
  E = vector(3, j, 0*T8);   \\ E = sum_{x != 0} omega(x) [Tr x] in Z[zeta_8][C_3]
  a = 1; b = 0;
  for (k = 0, 7,
     tr = (2*a) % 3;  E[tr+1] += T8^k;
     [a, b] = [(a - b) % 3, (a + b) % 3]);   \\ multiply by (1+i)
  E2 = E + [1,1,1];                          \\ + N_{C_3}: value q at trivial psi, Gauss sum elsewhere
  print("(72,8) Gauss element E'' coefficients in Z[zeta_8]: ", lift(E2));
  A = vector(9, y, if ((y-1) % 3 == 0, E2[(y-1)/3 + 1], 0*T8));   \\ inflate along T -> T^3
  B = vector(8);  \\ perfect quaternary sequence of length 8 (searched below)
  found = 0;
  forvec(v = vector(8, i, [0, 3]), if (!found,
     bb = vector(8, i, T8^(2*v[i]));
     ok = 1; for (s = 1, 7, if (sum(x = 0, 7, bb[x+1] * cnj(bb[((x - s) % 8) + 1], 8)) != 0, ok = 0; break));
     if (ok, B = bb; found = 1)));
  print("   perfect quaternary length-8 B: ", lift(B));
  D = matrix(9, 8, y, x, A[y] * B[x]);
  report("(72,8) Gauss-type fake  D = E''(T^3) (x) B", D, h, q, 72);
  \\ valuations at the two primes over 3 for a primitive order-9 character, per H-character
  K = nfinit(polcyclo(72, z)); P = idealprimedec(K, 3);
  print("   primes over 3 in Q(zeta72): ", #P, ", e = ", P[1].e, ", f = ", P[1].f);
  for (l = 0, 7, zz = lift(chival(D, h, 72, 1, l));
     print("   psi order 9, phi_", l, ":  (v_P1, v_P2) = (", idealval(K, zz, P[1]), ", ", idealval(K, zz, P[2]), ")   [uniform would be (6,6)]"));
  zz = lift(chival(D, h, 72, 3, 0));
  print("   psi order 3: (", idealval(K, zz, P[1]), ", ", idealval(K, zz, P[2]), ")");
}

\\ ---------- scalar-on-Sylow fakes: D = gamma[0] (x) Chu_m,  gamma in Z[zeta_h], gamma*conj = q^2, q !| gamma ----------
fake_scalar(name, h, q, m, gam, N) = {
  my(B = chu(m, h), D = matrix(q^2, m, y, x, if (y == 1, gam*B[x], 0)));
  print("   gamma*conj(gamma) = ", lift(gam * cnj(gam, h)));
  report(name, D, h, q, N);
}
\\ quadratic Gauss sums: s11 = sqrt(-11), s5 = sqrt(5), s7 = sqrt(-7), as elements of Z[zeta_h]
s11(h) = { my(z11 = Mod(t, polcyclo(h,t))^(h/11)); sum(x=1,10, kronecker(x,11)*z11^x); }
s5(h)  = { my(z5 = Mod(t, polcyclo(h,t))^(h/5)); sum(x=1,4, kronecker(x,5)*z5^x); }
s7(h)  = { my(z7 = Mod(t, polcyclo(h,t))^(h/7)); sum(x=1,6, kronecker(x,7)*z7^x); }
{

  \\ (45,35): q=3, gamma = (1 + sqrt(-35))/2, norm 9
  h = 35; g = (1 + s5(h)*s7(h))/2;  fake_scalar("(45,35) extreme fake", h, 3, 5, g, 315);
  \\ (99,77): q=3, gamma = ((1+sqrt(-11))/2)^2
  h = 77; g = ((1 + s11(h))/2)^2;    fake_scalar("(99,77) extreme fake", h, 3, 11, g, 693);
  \\ (100,44): q=5, gamma = ((3+sqrt(-11))/2)^2
  h = 44; g = ((3 + s11(h))/2)^2;    fake_scalar("(100,44) extreme fake", h, 5, 4, g, 1100);
  \\ (90,20): q=3, gamma = 2 + sqrt(-5), sqrt(-5) = sqrt(5)*i
  h = 20; g = 2 + s5(h)*Mod(t^5, polcyclo(20,t)); fake_scalar("(90,20) extreme fake", h, 3, 10, g, 180);
  \\ (63,91): q=3, gamma in Z[zeta_13] (gamma13.gp: (gamma) = P1^2 P2^2, gamma*conj = 9), zeta_13 = t^7
  h = 91; z13 = Mod(t, polcyclo(91,t))^7;
  g = 2*z13^10 + 2*z13^9 + 2*z13^7 + z13^6 + 2*z13^5 + z13^4 + 2*z13^3 + 2*z13^2 + z13 + 1;
  fake_scalar("(63,91) extreme fake", h, 3, 7, g, 819);
}
quit;
