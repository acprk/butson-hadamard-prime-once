// Enumerate B: T -> mu_m (T subset of Z_n, |T|=k, B[T[0]]=1) with B B^* = k * delta  (group-invariant weighing).
// usage: wsearch n m t0 t1 ... t_{k-1}   prints count and solutions (exponents)
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <complex.h>
#include "phi42.h"
int n,m,k,T[64],e[64]; long cnt=0; double complex z[256];
int lastidx[256]; // for each difference g, the max index (in T order) among pairs realising g
int pairs[256][128][2], np[256];
int printmax=50;
void check_and_rec(int i){
  if(i==k){ cnt++; if(cnt<=printmax){ for(int j=0;j<k;j++) printf("%d ",e[j]); printf("\n"); } return; }
  for(int a=0;a<m;a++){
    if(i==0 && a!=0) break;
    e[i]=a; int ok=1;
    for(int g=1; g<n && ok; g++){
      if(lastidx[g]!=i) continue;
      long v[DEG]={0};
      for(int p=0;p<np[g];p++){ int x=pairs[g][p][0], y=pairs[g][p][1]; {int aa=((e[x]-e[y])%m+m)%m; for(int t=0;t<DEG;t++) v[t]+=RED[aa][t];} }
      for(int t=0;t<DEG;t++) if(v[t]) ok=0;
    }
    if(ok) check_and_rec(i+1);
  }
}
int main(int argc,char**argv){
  n=atoi(argv[1]); m=atoi(argv[2]); k=argc-3; for(int i=0;i<k;i++) T[i]=atoi(argv[3+i]);
  if(argc>3+k) ;
  char*pm=getenv("PRINTMAX"); if(pm) printmax=atoi(pm);
  for(int a=0;a<m;a++) z[a]=cexp(2*M_PI*I*a/m);
  for(int g=0;g<n;g++){np[g]=0; lastidx[g]=-1;}
  for(int i=0;i<k;i++) for(int j=0;j<k;j++) if(i!=j){ int g=((T[i]-T[j])%n+n)%n; pairs[g][np[g]][0]=i; pairs[g][np[g]][1]=j; np[g]++; int mx=i>j?i:j; if(mx>lastidx[g]) lastidx[g]=mx; }
  check_and_rec(0);
  fprintf(stderr,"count %ld\n",cnt); printf("count %ld\n",cnt);
  return 0;
}
