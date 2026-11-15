/* coulombidx.c -- Coulomb index of n centers, sum over permutations of the
   recursion for the partial indices F and G of CoulombHiggs.m (CoulombFOpt, CoulombGOpt),
   translated line by line, in double precision.

   Input (stdin):  one or several problems, each given as: n, nthreads, noloop flag,
                   then the integer matrix E (n x n) giving the y-exponent  sum_{i<j} E[s_i][s_j],
                   then the perturbed DSZ matrix P (n x n, doubles),
                   then the perturbed FI vector c (n doubles).
   Output (stdout): for each problem, lines "e v": sum over permutations s with exponent e of
                   F(P_s, c_s), possibly a line "AMBIGUOUS k" (a sign test was within roundoff of zero),
                   and a final line "END".
   The values of F are dyadic rationals (sums of products of +-1, +-1/2), exact in double.
   Prefactor (y-1/y)^(1-n) (-1)^(...) is applied by the caller.
   Build: cc -O3 -o coulombidx coulombidx.c -lpthread                                     */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <pthread.h>

#define NMAX 16
#define TOL 0.0
#define M(a,m,i,j) a[((i)-1)*(m)+((j)-1)]   /* 1-based access to m x m matrix */

static int noloop = 0;
/* roundoff guard: a sign test is "ambiguous" if |value| < GUARD * (sum of |terms|) */
#define GUARD 1e-13
static volatile long ambiguous = 0;
static void chk(double v,double mag){ if(mag>0 && fabs(v)<GUARD*mag) ambiguous++; }
/* sum of a(i,j) over i in [i0,i1], j in [max(i+1,j0)..j1] (j0<=0 means i+1), returns abs-sum in *mag */
static double rsum(const double *a,int m,int i0,int i1,int j0,int j1,double *mag){
  double s=0,t=0;
  for(int i=i0;i<=i1;i++){ int js = j0>0 ? j0 : i+1; for(int j=js;j<=j1;j++){ double v=M(a,m,i,j); s+=v; t+=fabs(v);} }
  if(mag) *mag+=t; return s; }

static int sgnpos(double x){ return x>0 ? 1 : -1; }

/* Take rows/cols lo..hi of m x m matrix a into b ((hi-lo+1) square) */
static void take(const double *a,int m,int lo,int hi,double *b){
  int r=hi-lo+1;
  for(int i=lo;i<=hi;i++) for(int j=lo;j<=hi;j++) M(b,r,i-lo+1,j-lo+1)=M(a,m,i,j);
}

/* MatmuOpt */
static void matmu(const double *a,int m,double mu,double *b){
  memcpy(b,a,sizeof(double)*m*m);
  for(int i=1;i<=m;i++){ M(b,m,i,m)*=mu; M(b,m,m,i)*=mu; }
  double s=0; for(int k=1;k<=m-1;k++) s+=M(a,m,k,m);
  M(b,m,m-3,m-1)=M(a,m,m-3,m-1)+(1-mu)*s;
  M(b,m,m-1,m-3)=-M(b,m,m-3,m-1);
}

/* MatRedOpt[Mat,k]: k x k */
static void matred(const double *a,int m,int k,double *b){
  take(a,m,1,k,b);
  for(int i=1;i<=k-1;i++){ double s=0; for(int j=k;j<=m;j++) s+=M(a,m,i,j);
    M(b,k,i,k)=s; M(b,k,k,i)=-s; }
}

/* MatRedOpt2[Mat,k]: (k+1) x (k+1) */
static void matred2(const double *a,int m,int k,double *b){
  int r=k+1; take(a,m,1,k+1,b);
  for(int i=1;i<=k-1;i++){ double s=0; for(int j=k;j<=m-1;j++) s+=M(a,m,i,j);
    M(b,r,i,k)=s; M(b,r,i,k+1)=M(a,m,i,m); M(b,r,k,i)=-s; M(b,r,k+1,i)=-M(a,m,i,m); }
  double s=0; for(int i=k;i<=m-1;i++) s+=M(a,m,i,m);
  M(b,r,k,k+1)=s; M(b,r,k+1,k)=-s;
}

static double la(const double *a,int m,int k){
  double num=0,den=0;
  for(int s=k+1;s<=m-2;s++) for(int j=s+1;j<=m-1;j++) num+=M(a,m,s,j);
  for(int s=k+1;s<=m-1;s++) den+=M(a,m,s,m);
  return -num/den;
}

/* MNewFOpt: (k+1) x (k+1) */
static void mnewf(const double *a,int m,int k,double *b){
  int r=k+1; double l=la(a,m,k);
  for(int i=1;i<=r;i++) for(int j=1;j<=r;j++) M(b,r,i,j)=0;
  for(int i=1;i<=k;i++){
    for(int j=1;j<=k;j++) M(b,r,i,j)=M(a,m,i,j);
    double s=0; for(int j=k+1;j<=m-1;j++) s+=M(a,m,i,j);
    s+=M(a,m,i,m)*l;
    M(b,r,i,r)=s; M(b,r,r,i)=-s;
  }
}
/* MNewGOpt: (m-k) x (m-k) */
static void mnewg(const double *a,int m,int k,double *b){
  int r=m-k; double l=la(a,m,k);
  for(int i=1;i<=r;i++) for(int j=1;j<=r;j++) M(b,r,i,j)=0;
  for(int i=k+1;i<=m-1;i++){
    for(int j=k+1;j<=m-1;j++) M(b,r,i-k,j-k)=M(a,m,i,j);
    M(b,r,i-k,r)=l*M(a,m,i,m); M(b,r,r,i-k)=-l*M(a,m,i,m);
  }
}

static double G(const double *a,int m);

static double F(const double *a,const double *c,int m){
  if(m==1) return 1;
  if(m<1) return 0;
  double res=0;
  double b[NMAX*NMAX], cc[NMAX], g[NMAX*NMAX];
  if(M(a,m,m-1,m)*c[m-1]<0){
    take(a,m,1,m-1,b);
    for(int i=0;i<m-2;i++) cc[i]=c[i];
    cc[m-2]=c[m-2]+c[m-1];
    res+= (M(a,m,m-1,m)>0 ? 1 : -1)*F(b,cc,m-1);
  }
  if(!noloop){
    for(int k=0;k<=m-3;k++){
      double mA=0,mB=0,ms=0;
      double A=-rsum(a,m,k+1,m-1,0,m,&mA);
      double B=rsum(a,m,k+1,m-2,0,m-1,&mB);
      double s=0; for(int i=k+1;i<=m-1;i++){ s+=M(a,m,i,m); ms+=fabs(M(a,m,i,m)); }
      chk(A,mA); chk(B,mB); chk(s,ms);
      double P=A*B, fac;
      if(P>TOL) fac=1; else if(fabs(P)<=TOL) fac=0.5; else continue;
      mnewf(a,m,k,b);
      for(int i=0;i<k;i++) cc[i]=c[i];
      { double t=0; for(int i=k;i<m;i++) t+=c[i]; cc[k]=t; }
      double f=F(b,cc,k+1);
      if(f==0) continue;
      mnewg(a,m,k,g);
      res+= fac*sgnpos(s)*f*G(g,m-k);
    }
  }
  return res;
}

static double G(const double *a,int m){
  if(m==3){ double p=M(a,m,1,2)*M(a,m,2,3); return p>0 ? (M(a,m,1,2)>0?1:-1) : 0; }
  if(m<=2) return 1;
  double b[NMAX*NMAX], d[NMAX*NMAX], e[NMAX*NMAX];
  double S=0,mS=0; for(int i=1;i<=m-1;i++){ S+=M(a,m,i,m); mS+=fabs(M(a,m,i,m)); }
  chk(S,mS);
  double g=0;
  /* value at mu=0 (the 1/2 branch of the Mathematica code is unreachable, see note) */
  if(M(a,m,m-1,m)*S<0){
    matmu(a,m,0,b); take(b,m,1,m-1,d);
    g+= (M(a,m,m-1,m)>0?1:-1)*G(d,m-1);
  }
  /* type 1 */
  { double mu1=-M(a,m,m-2,m-1)/(M(a,m,m-2,m)+M(a,m,m-1,m));
    double q1=M(a,m,m-2,m-1)+M(a,m,m-1,m)+M(a,m,m-2,m);
    chk(q1,fabs(M(a,m,m-2,m-1))+fabs(M(a,m,m-1,m))+fabs(M(a,m,m-2,m)));
    chk(M(a,m,m-2,m)+M(a,m,m-1,m),fabs(M(a,m,m-2,m))+fabs(M(a,m,m-1,m)));
    double Q=q1*M(a,m,m-2,m-1), fac=0;
    if(Q<-TOL) fac=1; else if(fabs(Q)<=TOL) fac=0.5;
    if(fac!=0){
      matmu(a,m,mu1,b); matred(b,m,m-2,d); take(b,m,m-2,m,e);
      g+= fac*sgnpos(M(a,m,m-2,m)+M(a,m,m-1,m))*G(d,m-2)*G(e,3);
    }
  }
  /* type 2, k=2 */
  if(m>4){
    double mX=0,mY=mS;
    double X=rsum(a,m,2,m-1,0,m,&mX);
    double Y=rsum(a,m,2,m-2,0,m-1,&mY)+S;
    chk(X,mX); chk(Y,mY);
    if(X*Y<0){
      double mu2=Y/M(a,m,1,m);
      matmu(a,m,mu2,b); take(b,m,2,m,d);
      g+= (M(a,m,1,m)>0 ? -1 : 1)*G(d,m-1);
    }
  }
  /* type 2, k>2 */
  for(int k=3;k<=m-3;k++){
    double mX=0,mY=mS,mU=0;
    double X=rsum(a,m,k,m-1,0,m,&mX);
    double Y=rsum(a,m,k,m-2,0,m-1,&mY)+S;
    double T=rsum(a,m,k,m-1,0,m-1,NULL);
    double U=0; for(int i=1;i<=k-1;i++){ U+=M(a,m,i,m); mU+=fabs(M(a,m,i,m)); }
    chk(X,mX); chk(Y,mY); chk(U,mU);
    double P=X*Y, fac=0;
    if(P<-TOL) fac=1; else if(fabs(P)<=TOL) fac=0.5;
    if(fac==0) continue;
    double mu3=(T+S)/U;
    matmu(a,m,mu3,b); matred(b,m,k,d); take(b,m,k,m,e);
    g+= fac*(U>0 ? -1 : 1)*G(d,k)*G(e,m-k+1);
  }
  /* type 3 */
  for(int k=2;k<=m-3;k++){
    double mZ=0;
    double Z=rsum(a,m,k,m-2,0,m-1,&mZ);
    double T=rsum(a,m,k,m-1,0,m-1,NULL);
    chk(Z,mZ); chk(Z+S,mZ+mS);
    double P=Z*(Z+S), fac=0;
    if(P<-TOL) fac=1; else if(fabs(P)<=TOL) fac=0.5;
    if(fac==0) continue;
    double mu4=(T+S)/S;
    matmu(a,m,mu4,b); matred2(b,m,k,d); take(b,m,k,m-1,e);
    g+= fac*(S>0 ? -1 : 1)*G(d,k+1)*G(e,m-k);
  }
  return g;
}

/* ---------------- driver: sum over permutations ---------------- */
static int n, nthreads;
static int E[NMAX][NMAX];
static double P0[NMAX][NMAX], C0[NMAX];
static int emin, erange;

typedef struct { int first; double *acc; } job_t;

static int next_perm(int *p,int len){
  int i=len-2; while(i>=0 && p[i]>p[i+1]) i--;
  if(i<0) return 0;
  int j=len-1; while(p[j]<p[i]) j--;
  int t=p[i]; p[i]=p[j]; p[j]=t;
  for(int a=i+1,b=len-1;a<b;a++,b--){ t=p[a]; p[a]=p[b]; p[b]=t; }
  return 1;
}

static void *work(void *arg){
  job_t *jb=(job_t*)arg;
  int p[NMAX], rest[NMAX], r=0;
  for(int i=0;i<n;i++) if(i!=jb->first) rest[r++]=i;
  double a[NMAX*NMAX], c[NMAX];
  do{
    p[0]=jb->first; for(int i=0;i<r;i++) p[i+1]=rest[i];
    int e=0;
    for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) e+=E[p[i]][p[j]];
    for(int i=0;i<n;i++){ c[i]=C0[p[i]]; for(int j=0;j<n;j++) a[i*n+j]=P0[p[i]][p[j]]; }
    double f=F(a,c,n);
    if(f!=0) jb->acc[e-emin]+=f;
  } while(next_perm(rest,r));
  return NULL;
}

static int solve_one(void){
  if(scanf("%d %d %d",&n,&nthreads,&noloop)!=3) return 0;
  if(n<1||n>NMAX) { fprintf(stderr,"n out of range\n"); return 0; }
  for(int i=0;i<n;i++) for(int j=0;j<n;j++) if(scanf("%d",&E[i][j])!=1) return 0;
  for(int i=0;i<n;i++) for(int j=0;j<n;j++) if(scanf("%lf",&P0[i][j])!=1) return 0;
  for(int i=0;i<n;i++) if(scanf("%lf",&C0[i])!=1) return 0;
  ambiguous=0;
  if(n==1){ printf("0 1\nEND\n"); return 1; }
  int tot=0; for(int i=0;i<n;i++) for(int j=0;j<n;j++) tot+=abs(E[i][j]);
  emin=-tot; erange=2*tot+1;
  job_t jobs[NMAX]; pthread_t th[NMAX];
  for(int f=0;f<n;f++){ jobs[f].first=f; jobs[f].acc=calloc(erange,sizeof(double)); }
  if(nthreads<1) nthreads=1;
  for(int f0=0;f0<n;f0+=nthreads){
    int f1=f0+nthreads; if(f1>n) f1=n;
    if(f1-f0==1) work(&jobs[f0]);
    else {
      for(int f=f0;f<f1;f++) pthread_create(&th[f],NULL,work,&jobs[f]);
      for(int f=f0;f<f1;f++) pthread_join(th[f],NULL);
    }
  }
  for(int e=0;e<erange;e++){
    double s=0; for(int f=0;f<n;f++) s+=jobs[f].acc[e];
    if(s!=0) printf("%d %.17g\n",e+emin,s);
  }
  for(int f=0;f<n;f++) free(jobs[f].acc);
  if(ambiguous) printf("AMBIGUOUS %ld\n",ambiguous);
  printf("END\n");
  return 1;
}

/* several problems may be given one after the other; each answer ends with a line END */
int main(void){
  while(solve_one()) ;
  return 0;
}
