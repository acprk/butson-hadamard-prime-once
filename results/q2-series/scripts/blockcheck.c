/* Independent brute-force check of the combinatorial half of Theorem E1 for n=36 (q=3), small h.
   Input of the check = ONLY the output of the descent lemma (single-class concentration):
   for each s in {1,2}, j in Z4, exactly one class rho in Z3 has B_{j,rho}(s) != 0, and then |B|^2 = 36
   at every embedding.  Here B_{j,rho}(s) = sum_{y,t} i^{jy} zeta_h^{e[y][t]} omega^{st}, block = 4x3 array
   e[y][t] = exponent of C_y(rho+3t).
   Step 1: enumerate all h^12 blocks, keep those with every B_{j}(s) in {0} U {norm 36} (8-bit mask of nonzeros).
   Step 2: all ordered triples of kept blocks with disjoint masks covering all 8 (j,s).
   Step 3: test full perfectness |D(chi)|^2 = 36 for all 36 characters at all embeddings.
   usage: blockcheck h [maxprint]                                                                     */
#include <stdio.h>
#include <stdlib.h>
#include <complex.h>
#include <math.h>
static int gcd(int a,int b){while(b){int t=a%b;a=b;b=t;}return a;}
int h,M,nemb,emb[64];
double complex Z[64][256]; /* Z[k][x] = exp(2 pi i x u_k / M) */
typedef struct { unsigned char e[12]; unsigned char mask; } blk;
blk *kept; long nkept=0, cap=0;
int main(int argc,char**argv){
  h=atoi(argv[1]); int maxprint=(argc>2&&argv[2][0]!='t')?atoi(argv[2]):5;
  M=12*h/gcd(12,h); /* lcm(12,h) */
  int M36 = 36*h/gcd(36,h); (void)M36;
  nemb=0; for(int u=1;u<M;u++) if(gcd(u,M)==1) emb[nemb++]=u;
  for(int k=0;k<nemb;k++) for(int x=0;x<M;x++) Z[k][x]=cexp(2*M_PI*I*(double)((long)x*emb[k]%M)/M);
  int eh=M/h, eo=M/3, ei=M/4;
  /* fibre DFT table: fibre f = (e0,e1,e2) in Z_h^3, A[f][s][k] */
  int nf=h*h*h;
  double complex (*A)[3][64]=malloc(sizeof(double complex)*nf*3*64);
  for(int f=0;f<nf;f++){int e0=f%h,e1=(f/h)%h,e2=f/(h*h); int ee[3]={e0,e1,e2};
    for(int s=0;s<3;s++) for(int k=0;k<nemb;k++){double complex v=0; for(int t=0;t<3;t++) v+=Z[k][(ee[t]*eh+s*t*eo)%M]; A[f][s][k]=v;}}
  long total=(long)nf*nf*nf*nf;
  int testmode = argc>2 && argv[2][0]=='t';
  long testf[3][4];
  if(testmode){ int ex[36]; for(int g=0;g<36;g++) if(scanf("%d",&ex[g])!=1) return 1;
    for(int r=0;r<3;r++) for(int y=0;y<4;y++){ long ff=0, mul=1; for(int t=0;t<3;t++){ int w=r+3*t; int g=-1; for(int gg=0;gg<36;gg++) if(gg%4==y && gg%9==w) g=gg; ff+=ex[g]%h*mul; mul*=h;} testf[r][y]=ff; } total=3; }
  for(long b=0;b<total;b++){
    int f[4]; long bb=b; for(int y=0;y<4;y++){f[y]=bb%nf; bb/=nf;}
    if(testmode) for(int y=0;y<4;y++) f[y]=testf[b][y];
    unsigned char mask=0; int ok=1;
    for(int s=1;s<=2&&ok;s++) for(int j=0;j<4&&ok;j++){
      int nz=-1;
      for(int k=0;k<nemb;k++){
        double complex v=0; for(int y=0;y<4;y++) v+=Z[k][(j*y*ei)%M]*A[f[y]][s][k];
        double a2=creal(v*conj(v));
        int z = a2<1e-9, n36 = fabs(a2-36.0)<1e-6;
        if(!z && !n36){ok=0;break;}
        if(nz==-1) nz = z?0:1; else if(nz != (z?0:1)){ok=0;break;}
      }
      if(ok && nz==1) mask |= 1<<((s-1)*4+j);
    }
    if(!ok) continue;
    if(nkept==cap){cap=cap?2*cap:1<<16; kept=realloc(kept,cap*sizeof(blk));}
    for(int y=0;y<4;y++){int ff=f[y]; for(int t=0;t<3;t++){kept[nkept].e[y*3+t]=ff%h; ff/=h;}}
    kept[nkept].mask=mask; nkept++;
  }
  long bymask[256]={0}; for(long a=0;a<nkept;a++) bymask[kept[a].mask]++;
  printf("h=%d M=%d: blocks %ld, admissible %ld; masks:",h,M,total,nkept);
  for(int m=0;m<256;m++) if(bymask[m]) printf(" %02x:%ld",m,bymask[m]); printf("\n");
  /* index by mask */
  long *start=calloc(257,sizeof(long)); for(int m=0;m<256;m++) start[m+1]=start[m]+bymask[m];
  long *idx=malloc(sizeof(long)*(nkept+1)); long *fill=calloc(256,sizeof(long));
  for(long a=0;a<nkept;a++){int m=kept[a].mask; idx[start[m]+fill[m]++]=a;}
  /* characters of Z36 = C4 x C9 at embeddings of Q(zeta_{lcm(36,h)}) */
  int L=36*h/gcd(36,h); int ne=0, eu[256]; for(int u=1;u<L;u++) if(gcd(u,L)==1) eu[ne++]=u;
  long ntrip=0, nperf=0;
  for(int m0=0;m0<256;m0++) if(bymask[m0]) for(int m1=0;m1<256;m1++) if(bymask[m1] && !(m0&m1)){
    int m2 = 0xff & ~(m0|m1); if(!bymask[m2]) continue;
    for(long a0=start[m0];a0<start[m0+1];a0++) for(long a1=start[m1];a1<start[m1+1];a1++) for(long a2=start[m2];a2<start[m2+1];a2++){
      ntrip++;
      blk *B3[3]={&kept[idx[a0]],&kept[idx[a1]],&kept[idx[a2]]};
      int ex[4][9]; for(int r=0;r<3;r++) for(int y=0;y<4;y++) for(int t=0;t<3;t++) ex[y][r+3*t]=B3[r]->e[y*3+t];
      int ok=1;
      for(int k=0;k<ne&&ok;k++) for(int j=0;j<4&&ok;j++) for(int c=0;c<9&&ok;c++){
        double complex v=0;
        for(int y=0;y<4;y++) for(int w=0;w<9;w++){
          long x = ((long)ex[y][w]*(L/h) + (long)j*y*(L/4) + (long)c*w*(L/9)) % L;
          v += cexp(2*M_PI*I*(double)(x*eu[k]%L)/L);
        }
        if(fabs(creal(v*conj(v))-36.0)>1e-6) ok=0;
      }
      if(ok){ nperf++; if(nperf<=maxprint){ printf("perfect:"); for(int g=0;g<36;g++) printf(" %d",ex[g%4][g%9]); printf("\n");} }
    }
  }
  printf("h=%d: ordered class-triples with complementary masks %ld; perfect %ld\n",h,ntrip,nperf);
  return 0;
}
