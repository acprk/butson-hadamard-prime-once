/* Independent exhaustive search for perfect sequences of length n=4q over mu_h (BH(Z_{4q},h)), q odd prime in {3,5}.
   Z_{4q} = C4 x Cq (CRT), column w in Cq = (x[g])_{g = y mod 4} with g = w mod q.  For each character psi of C4
   (T -> i^psi) put c_w(psi) = sum_y z^{col_w[y]} i^{psi y}.  D perfect  <=>  for every psi the vector (c_w(psi))_w
   has C_q-autocorrelation 4q*delta  (R_0 = 4q, R_s = 0 for s=1..(q-1)/2).
   Enumeration: col0 over orbit representatives (x0=0) under Galois (Z/h)^*, cyclic rotation of the column (T-shift)
   and reversal (g -> -g); weight = orbit size.  If q | h, col1[0] < h/q (chirp g -> zeta_q^{k g}); weight *q.
   cols 1..q-2 enumerated, col_{q-1} solved from R_1(psi)=0 (real-linear 2x2, unique if |c_{q-2}|!=|c_0|, else <=2
   points on the norm circle), looked up by value, then all conditions verified; final hits re-verified by direct
   periodic autocorrelation at every embedding j in (Z/h)^*.
   usage: ./bhcol q h [print]          test mode: ./bhcol q h test x0 ... x_{n-1}  (fix cols 0..q-3, enumerate q-2)   */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <complex.h>
typedef double complex cx;
static int q, h, n, H4, prt = 0;
static cx zt[4096], (*C)[4]; static int *srt[4]; static double *re[4];
static cx IP[4][4];
static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static void decode(int id, int *x) { for (int y = 0; y < 4; y++) { x[y] = id % h; id /= h; } }
static int encode(const int *x) { int id = 0; for (int y = 3; y >= 0; y--) id = id * h + ((x[y] % h) + h) % h; return id; }
static int cmpk; static int cmpre(const void *A, const void *B) { double a = re[cmpk][*(int*)A], b = re[cmpk][*(int*)B]; return a < b ? -1 : a > b; }
static int lower(int k, double v) { int lo = 0, hi = H4; while (lo < hi) { int m = (lo + hi) / 2; if (re[k][srt[k][m]] < v) lo = m + 1; else hi = m; } return lo; }
static int fullcheck(int *cid) { /* exact-ish autocorrelation at all embeddings */
  int x[64];
  for (int g = 0; g < n; g++) { int col[4]; decode(cid[g % q], col); x[g] = col[g % 4]; }
  for (int j = 1; j < h || (h == 1 && j == 1); j++) { if (gcd(j, h) != 1) continue;
    for (int s = 1; s < n; s++) { cx a = 0; for (int g = 0; g < n; g++) a += zt[(long)j * ((x[(g + s) % n] - x[g] + h) % h) % h]; if (cabs(a) > 1e-7) return 0; }
    if (h == 1) break; }
  return 1;
}
static long hits = 0; static double whits = 0;
static int cid[16];
/* given cols 0..q-2 in cid, find all last columns */
static void solve_last(double wt) {
  cx c[16][4]; for (int w = 0; w < q - 1; w++) for (int k = 0; k < 4; k++) c[w][k] = C[cid[w]][k];
  int best = -1, bestdeg = 3; cx cand[4][2]; int nc[4];
  double R2[4];
  for (int k = 0; k < 4; k++) {
    cx r = 0; double nn = 0;
    for (int w = 0; w + 1 <= q - 2; w++) r -= c[w + 1][k] * conj(c[w][k]);
    for (int w = 0; w < q - 1; w++) nn += creal(c[w][k] * conj(c[w][k]));
    R2[k] = 4.0 * q - nn; if (R2[k] < -1e-9) return; if (R2[k] < 0) R2[k] = 0;
    cx u = c[q - 2][k], v = c[0][k]; double det = creal(u * conj(u)) - creal(v * conj(v));
    if (fabs(det) > 1e-9) { cand[k][0] = (r * u - conj(r) * v) / det; nc[k] = 1; if (fabs(creal(cand[k][0] * conj(cand[k][0])) - R2[k]) > 1e-6) return; if (bestdeg > 0) { best = k; bestdeg = 0; } }
    else { double m = cabs(u); if (m < 1e-9) { nc[k] = -1; continue; }
      double al = carg(u), be = carg(v); cx t = (r / m) * cexp(-I * (be - al) / 2) / 2;
      if (fabs(cimag(t)) > 1e-7) return;
      double ry = creal(t); double d2 = R2[k] - ry * ry; if (d2 < -1e-7) return; if (d2 < 0) d2 = 0;
      cx ph = cexp(I * (al + be) / 2); cand[k][0] = (ry + I * sqrt(d2)) * ph; cand[k][1] = (ry - I * sqrt(d2)) * ph;
      nc[k] = (d2 < 1e-12) ? 1 : 2; if (bestdeg > 1) { best = k; bestdeg = 1; } }
  }
  if (best < 0) { fprintf(stderr, "all psi uninformative?!\n"); exit(1); }
  for (int t = 0; t < nc[best]; t++) {
    cx tg = cand[best][t]; int i = lower(best, creal(tg) - 1e-7);
    for (; i < H4 && re[best][srt[best][i]] <= creal(tg) + 1e-7; i++) {
      int id = srt[best][i]; if (cabs(C[id][best] - tg) > 1e-6) continue;
      /* verify all psi, all shifts */
      int ok = 1;
      for (int k = 0; k < 4 && ok; k++) { cx v[16]; for (int w = 0; w < q - 1; w++) v[w] = c[w][k]; v[q - 1] = C[id][k];
        double r0 = 0; for (int w = 0; w < q; w++) r0 += creal(v[w] * conj(v[w])); if (fabs(r0 - 4.0 * q) > 1e-6) ok = 0;
        for (int s = 1; s <= (q - 1) / 2 && ok; s++) { cx a = 0; for (int w = 0; w < q; w++) a += v[(w + s) % q] * conj(v[w]); if (cabs(a) > 1e-6) ok = 0; } }
      if (!ok) continue;
      cid[q - 1] = id;
      if (!fullcheck(cid)) { fprintf(stderr, "float hit failed full check\n"); continue; }
      hits++; whits += wt;
      if (prt) { int x[64]; for (int g = 0; g < n; g++) { int col[4]; decode(cid[g % q], col); x[g] = col[g % 4]; } for (int g = 0; g < n; g++) printf("%d ", x[g]); printf("\n"); }
    }
  }
}
static int units[4096], nu;
static int canon(const int *x) { /* min encoding over Galois x rotation x reversal, normalized x0=0 */
  int best = 1 << 30;
  for (int a = 0; a < nu; a++) for (int r = 0; r < 4; r++) for (int rv = 0; rv < 2; rv++) {
    int y[4]; for (int k = 0; k < 4; k++) { int src = rv ? ((r - k) % 4 + 4) % 4 : (k + r) % 4; y[k] = (int)((long)units[a] * x[src] % h); }
    int b = y[0]; for (int k = 0; k < 4; k++) y[k] = ((y[k] - b) % h + h) % h;
    int e = encode(y); if (e < best) best = e; }
  return best;
}
int main(int argc, char **argv) {
  q = atoi(argv[1]); h = atoi(argv[2]); n = 4 * q; H4 = h * h * h * h;
  int test = argc > 3 && !strcmp(argv[3], "test"); prt = argc > 3 && !strcmp(argv[3], "print");
  for (int e = 0; e < h; e++) zt[e] = cexp(2 * M_PI * I * e / h);
  for (int p = 0; p < 4; p++) for (int y = 0; y < 4; y++) IP[p][y] = cpow(I, p * y);
  for (int p = 0; p < 4; p++) for (int y = 0; y < 4; y++) { int m = (p * y) % 4; IP[p][y] = m == 0 ? 1 : m == 1 ? I : m == 2 ? -1 : -I; }
  C = malloc(sizeof(cx[4]) * H4);
  for (int id = 0; id < H4; id++) { int x[4]; decode(id, x); for (int p = 0; p < 4; p++) { cx s = 0; for (int y = 0; y < 4; y++) s += zt[x[y]] * IP[p][y]; C[id][p] = s; } }
  for (int k = 0; k < 4; k++) { re[k] = malloc(sizeof(double) * H4); srt[k] = malloc(sizeof(int) * H4);
    for (int id = 0; id < H4; id++) { re[k][id] = creal(C[id][k]); srt[k][id] = id; } cmpk = k; qsort(srt[k], H4, sizeof(int), cmpre); }
  nu = 0; for (int a = 1; a <= h; a++) if (gcd(a, h) == 1) units[nu++] = a % h;
  if (test) { /* fix cols 0..q-3 from given sequence, enumerate col q-2 over all, solve last */
    int x[64]; for (int g = 0; g < n; g++) x[g] = atoi(argv[4 + g]);
    for (int w = 0; w < q; w++) { int col[4]; for (int g = 0; g < n; g++) if (g % q == w) col[g % 4] = x[g]; cid[w] = encode(col); }
    int want = cid[q - 1], wantm = cid[q-2]; long before = hits; int found = 0;
    for (int id = 0; id < H4; id++) { cid[q - 2] = id; long hb = hits; solve_last(1); if (hits > hb && id == wantm) found = 1; }
    printf("test: hits %ld, original sequence recovered: %s\n", hits - before, found ? "yes" : "no"); (void)want; return 0; }
  /* col0 representatives */
  int H3 = h * h * h; int lim1 = (h % q == 0) ? h / q : h; double chirpw = (h % q == 0) ? q : 1;
  int nrep = 0; long totorb = 0; int *cn = malloc(sizeof(int) * H3); long *orbc = calloc(H4, sizeof(long));
  for (int t = 0; t < H3; t++) { int x[4] = {0, t % h, (t / h) % h, t / (h * h)}; cn[t] = canon(x); orbc[cn[t]]++; }
  for (int t = 0; t < H3; t++) { int x[4] = {0, t % h, (t / h) % h, t / (h * h)}; int e = encode(x); if (cn[t] != e) continue;
    long orb = orbc[e];
    totorb += orb; nrep++;
    cid[0] = e;
    if (q == 3) { for (int id = 0; id < H4; id++) { if (id % h >= lim1) continue; cid[1] = id; solve_last(orb * chirpw); } }
    else if (q == 5) { for (int i1 = 0; i1 < H4; i1++) { if (i1 % h >= lim1) continue; cid[1] = i1;
        for (int i2 = 0; i2 < H4; i2++) { cid[2] = i2; for (int i3 = 0; i3 < H4; i3++) { cid[3] = i3; solve_last(orb * chirpw); } } } }
    fprintf(stderr, "rep %d done (orbit %ld), hits so far %ld\n", nrep, orb, hits);
  }
  printf("q=%d h=%d n=%d: col0 reps %d (orbit total %ld = h^3? %d), raw hits %ld, weighted count of normalized (x[0]=0) perfect sequences = %.0f\n",
         q, h, n, nrep, totorb, (int)(totorb == H3), hits, whits);
  return 0;
}
