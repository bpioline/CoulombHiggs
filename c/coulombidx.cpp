/* coulombidx.cpp -- Coulomb index of n centres: sum over permutations of the recursion for the
   partial indices F and G of CoulombHiggs.m (CoulombFOpt, CoulombGOpt), translated line by line.

   Input (stdin): one or several problems, each given as
        n  nthreads  noloop
        E (n x n integers): the y-exponent of an ordering s is sum_{i<j} E[s_i][s_j]
        P (n x n): perturbed DSZ matrix        c (n): perturbed FI vector
   Entries of P and c are exact rationals "p/q" (64-bit integers) or decimals.
   Output: for each problem, lines "e v" = sum over orderings s with exponent e of F(P_s, c_s),
   then possibly "AMBIGUOUS k", then "END".  F takes dyadic rational values, exact in double.

   Precision: each problem is done in double precision; every sign test is guarded (a tested sum
   is "ambiguous" if smaller than the guard times the sum of the absolute values of its terms).
   If any test is ambiguous, the problem is redone in double-double arithmetic (~32 digits,
   guard 1e-27), where values below the guard are exact zeros and treated as such (the original
   code then takes the half-weight branch); the output then contains DOUBLEDOUBLE and DDZEROS k.
   Build: c++ -O3 -std=c++17 -o coulombidx coulombidx.cpp -lpthread                          */

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <atomic>
#include <type_traits>
#include <vector>
#include <pthread.h>

#define NMAX 16
#define M(a,m,i,j) a[((i)-1)*(m)+((j)-1)]   /* 1-based access to an m x m matrix */

/* ---------------- double-double arithmetic ---------------- */
struct dd { double hi, lo; };
static inline dd two_sum(double a,double b){ double s=a+b, bb=s-a; return {s,(a-(s-bb))+(b-bb)}; }
static inline dd quick_two_sum(double a,double b){ double s=a+b; return {s,b-(s-a)}; }
static inline dd operator+(dd a,dd b){ dd s=two_sum(a.hi,b.hi); dd t=two_sum(a.lo,b.lo);
  s.lo+=t.hi; s=quick_two_sum(s.hi,s.lo); s.lo+=t.lo; return quick_two_sum(s.hi,s.lo); }
static inline dd operator-(dd a){ return {-a.hi,-a.lo}; }
static inline dd operator-(dd a,dd b){ return a+(-b); }
static inline dd operator*(dd a,dd b){ double p=a.hi*b.hi; double e=std::fma(a.hi,b.hi,-p);
  e+=a.hi*b.lo+a.lo*b.hi; return quick_two_sum(p,e); }
static inline dd operator/(dd a,dd b){ double q1=a.hi/b.hi; dd r=a-dd{q1,0}*b; double q2=r.hi/b.hi;
  r=r-dd{q2,0}*b; double q3=r.hi/b.hi; return quick_two_sum(q1,q2)+dd{q3,0}; }
static inline dd& operator+=(dd&a,dd b){ a=a+b; return a; }
static inline dd& operator*=(dd&a,dd b){ a=a*b; return a; }
static inline int sgn(double a){ return a>0 ? 1 : (a<0 ? -1 : 0); }
static inline int sgn(dd a){ return a.hi>0 ? 1 : (a.hi<0 ? -1 : sgn(a.lo)); }
static inline double hiv(double a){ return a; }
static inline double hiv(dd a){ return a.hi; }
template<class R> static inline R mk(double x);
template<> inline double mk<double>(double x){ return x; }
template<> inline dd mk<dd>(double x){ return dd{x,0}; }
template<class R> static inline double guard();
template<> inline double guard<double>(){ return 1e-13; }
template<> inline double guard<dd>(){ return 1e-27; }

/* rationals p/q are read exactly into dd */
static dd dd_from_ll(long long p){ double h=(double)p; long long r=p-(long long)h; return quick_two_sum(h,(double)r); }
static void parse_num(const char *s, double *d, dd *x){
  const char *slash=strchr(s,'/');
  if(slash && !strpbrk(s,".eE")){
    char *end; long long p=strtoll(s,&end,10); long long q=strtoll(slash+1,&end,10);
    *x=dd_from_ll(p)/dd_from_ll(q); *d=x->hi+x->lo; return;
  }
  *d=strtod(s,NULL); *x=dd{*d,0};
}

static int noloop = 0;
static std::atomic<long> ambiguous(0), ddzeros(0);

/* sign of a tested quantity v, with roundoff guard (mag = sum of |terms|).
   double: a value below the guard is flagged (the problem is then redone in double-double);
   double-double: a value below 1e-27 of its terms is an exact zero of the exact computation
   (genuine values are at least ~1e-25 of their terms with the package's perturbations), and is
   treated as such, as in the exact code (half-weight branch). */
template<class R> static inline int stest(R v,double mag){
  if(mag>0 && std::fabs(hiv(v))<guard<R>()*mag){
    if constexpr (std::is_same<R,dd>::value){ ddzeros++; return 0; }
    else ambiguous++;
  }
  return sgn(v);
}
/* sum of a(i,j), i in [i0,i1], j in [max(i+1,j0)..j1] (j0<=0 means i+1); adds sum of |terms| to *mag */
template<class R> static R rsum(const R *a,int m,int i0,int i1,int j0,int j1,double *mag){
  R s=mk<R>(0); double t=0;
  for(int i=i0;i<=i1;i++){ int js = j0>0 ? j0 : i+1;
    for(int j=js;j<=j1;j++){ s+=M(a,m,i,j); t+=std::fabs(hiv(M(a,m,i,j))); } }
  if(mag) *mag+=t; return s;
}
template<class R> static void take(const R *a,int m,int lo,int hi,R *b){
  int r=hi-lo+1;
  for(int i=lo;i<=hi;i++) for(int j=lo;j<=hi;j++) M(b,r,i-lo+1,j-lo+1)=M(a,m,i,j);
}
template<class R> static void matmu(const R *a,int m,R mu,R *b){          /* MatmuOpt */
  for(int i=0;i<m*m;i++) b[i]=a[i];
  for(int i=1;i<=m;i++){ M(b,m,i,m)*=mu; M(b,m,m,i)*=mu; }
  R s=mk<R>(0); for(int k=1;k<=m-1;k++) s+=M(a,m,k,m);
  M(b,m,m-3,m-1)=M(a,m,m-3,m-1)+(mk<R>(1)-mu)*s;
  M(b,m,m-1,m-3)=-M(b,m,m-3,m-1);
}
template<class R> static void matred(const R *a,int m,int k,R *b){         /* MatRedOpt: k x k */
  take(a,m,1,k,b);
  for(int i=1;i<=k-1;i++){ R s=mk<R>(0); for(int j=k;j<=m;j++) s+=M(a,m,i,j);
    M(b,k,i,k)=s; M(b,k,k,i)=-s; }
}
template<class R> static void matred2(const R *a,int m,int k,R *b){        /* MatRedOpt2: (k+1) x (k+1) */
  int r=k+1; take(a,m,1,k+1,b);
  for(int i=1;i<=k-1;i++){ R s=mk<R>(0); for(int j=k;j<=m-1;j++) s+=M(a,m,i,j);
    M(b,r,i,k)=s; M(b,r,i,k+1)=M(a,m,i,m); M(b,r,k,i)=-s; M(b,r,k+1,i)=-M(a,m,i,m); }
  R s=mk<R>(0); for(int i=k;i<=m-1;i++) s+=M(a,m,i,m);
  M(b,r,k,k+1)=s; M(b,r,k+1,k)=-s;
}
template<class R> static R la(const R *a,int m,int k){
  R num=mk<R>(0),den=mk<R>(0);
  for(int s=k+1;s<=m-2;s++) for(int j=s+1;j<=m-1;j++) num+=M(a,m,s,j);
  for(int s=k+1;s<=m-1;s++) den+=M(a,m,s,m);
  return -(num/den);
}
template<class R> static void mnewf(const R *a,int m,int k,R *b){          /* MNewFOpt: (k+1) x (k+1) */
  int r=k+1; R l=la(a,m,k);
  for(int i=0;i<r*r;i++) b[i]=mk<R>(0);
  for(int i=1;i<=k;i++){
    for(int j=1;j<=k;j++) M(b,r,i,j)=M(a,m,i,j);
    R s=mk<R>(0); for(int j=k+1;j<=m-1;j++) s+=M(a,m,i,j);
    s+=M(a,m,i,m)*l;
    M(b,r,i,r)=s; M(b,r,r,i)=-s;
  }
}
template<class R> static void mnewg(const R *a,int m,int k,R *b){          /* MNewGOpt: (m-k) x (m-k) */
  int r=m-k; R l=la(a,m,k);
  for(int i=0;i<r*r;i++) b[i]=mk<R>(0);
  for(int i=k+1;i<=m-1;i++){
    for(int j=k+1;j<=m-1;j++) M(b,r,i-k,j-k)=M(a,m,i,j);
    M(b,r,i-k,r)=l*M(a,m,i,m); M(b,r,r,i-k)=-(l*M(a,m,i,m));
  }
}

template<class R> static double G(const R *a,int m);

template<class R> static double F(const R *a,const R *c,int m){          /* CoulombFOpt */
  if(m==1) return 1;
  if(m<1) return 0;
  double res=0;
  R b[NMAX*NMAX], cc[NMAX], g[NMAX*NMAX];
  if(sgn(M(a,m,m-1,m))*sgn(c[m-1])<0){
    take(a,m,1,m-1,b);
    for(int i=0;i<m-2;i++) cc[i]=c[i];
    cc[m-2]=c[m-2]+c[m-1];
    res+= (sgn(M(a,m,m-1,m))>0 ? 1 : -1)*F(b,cc,m-1);
  }
  if(!noloop){
    for(int k=0;k<=m-3;k++){
      double mA=0,mB=0,ms=0;
      R A=-rsum(a,m,k+1,m-1,0,m,&mA);
      R B=rsum(a,m,k+1,m-2,0,m-1,&mB);
      R s=mk<R>(0); for(int i=k+1;i<=m-1;i++){ s+=M(a,m,i,m); ms+=std::fabs(hiv(M(a,m,i,m))); }
      int sP=stest(A,mA)*stest(B,mB), ss=stest(s,ms);
      double fac;
      if(sP>0) fac=1; else if(sP==0) fac=0.5; else continue;
      mnewf(a,m,k,b);
      for(int i=0;i<k;i++) cc[i]=c[i];
      { R t=mk<R>(0); for(int i=k;i<m;i++) t+=c[i]; cc[k]=t; }
      double f=F(b,cc,k+1);
      if(f==0) continue;
      mnewg(a,m,k,g);
      res+= fac*(ss>0 ? 1 : -1)*f*G(g,m-k);
    }
  }
  return res;
}

template<class R> static double G(const R *a,int m){                       /* CoulombGOpt */
  if(m==3){ int p=sgn(M(a,m,1,2))*sgn(M(a,m,2,3)); return p>0 ? (sgn(M(a,m,1,2))>0?1:-1) : 0; }
  if(m<=2) return 1;
  R b[NMAX*NMAX], d[NMAX*NMAX], e[NMAX*NMAX];
  R S=mk<R>(0); double mS=0; for(int i=1;i<=m-1;i++){ S+=M(a,m,i,m); mS+=std::fabs(hiv(M(a,m,i,m))); }
  int sS=stest(S,mS);
  double g=0;
  /* value at mu=0 (the 1/2 branch of CoulombGOpt is unreachable, see note) */
  { int p0=sgn(M(a,m,m-1,m))*sS;
    static int gfix = getenv("COULOMBIDX_GFIX")!=NULL;
    double fac0 = p0<0 ? 1 : ((p0==0 && gfix) ? 0.5 : 0);
    if(fac0!=0){
      matmu(a,m,mk<R>(0),b); take(b,m,1,m-1,d);
      g+= fac0*(sgn(M(a,m,m-1,m))>0?1:-1)*G(d,m-1);
    } }
  /* type 1 */
  { R q1=M(a,m,m-2,m-1)+M(a,m,m-1,m)+M(a,m,m-2,m);
    R q2=M(a,m,m-2,m)+M(a,m,m-1,m);
    int s1=stest(q1,std::fabs(hiv(M(a,m,m-2,m-1)))+std::fabs(hiv(M(a,m,m-1,m)))+std::fabs(hiv(M(a,m,m-2,m))));
    int s2=stest(q2,std::fabs(hiv(M(a,m,m-2,m)))+std::fabs(hiv(M(a,m,m-1,m))));
    int sQ=s1*sgn(M(a,m,m-2,m-1)); double fac=0;
    if(sQ<0) fac=1; else if(sQ==0) fac=0.5;
    if(fac!=0){
      R mu1=-(M(a,m,m-2,m-1)/q2);
      matmu(a,m,mu1,b); matred(b,m,m-2,d); take(b,m,m-2,m,e);
      g+= fac*(s2>0?1:-1)*G(d,m-2)*G(e,3);
    }
  }
  /* type 2, k=2 */
  if(m>4){
    double mX=0,mY=mS;
    R X=rsum(a,m,2,m-1,0,m,&mX);
    R Y=rsum(a,m,2,m-2,0,m-1,&mY)+S;
    if(stest(X,mX)*stest(Y,mY)<0){
      R mu2=Y/M(a,m,1,m);
      matmu(a,m,mu2,b); take(b,m,2,m,d);
      g+= (sgn(M(a,m,1,m))>0 ? -1 : 1)*G(d,m-1);
    }
  }
  /* type 2, k>2 */
  for(int k=3;k<=m-3;k++){
    double mX=0,mY=mS,mU=0;
    R X=rsum(a,m,k,m-1,0,m,&mX);
    R Y=rsum(a,m,k,m-2,0,m-1,&mY)+S;
    R T=rsum(a,m,k,m-1,0,m-1,(double*)NULL);
    R U=mk<R>(0); for(int i=1;i<=k-1;i++){ U+=M(a,m,i,m); mU+=std::fabs(hiv(M(a,m,i,m))); }
    int sP=stest(X,mX)*stest(Y,mY); int sU=stest(U,mU);
    double fac=0;
    if(sP<0) fac=1; else if(sP==0) fac=0.5;
    if(fac==0) continue;
    R mu3=(T+S)/U;
    matmu(a,m,mu3,b); matred(b,m,k,d); take(b,m,k,m,e);
    g+= fac*(sU>0 ? -1 : 1)*G(d,k)*G(e,m-k+1);
  }
  /* type 3 */
  for(int k=2;k<=m-3;k++){
    double mZ=0;
    R Z=rsum(a,m,k,m-2,0,m-1,&mZ);
    R T=rsum(a,m,k,m-1,0,m-1,(double*)NULL);
    int sP=stest(Z,mZ)*stest(Z+S,mZ+mS);
    double fac=0;
    if(sP<0) fac=1; else if(sP==0) fac=0.5;
    if(fac==0) continue;
    R mu4=(T+S)/S;
    matmu(a,m,mu4,b); matred2(b,m,k,d); take(b,m,k,m-1,e);
    g+= fac*(sS>0 ? -1 : 1)*G(d,k+1)*G(e,m-k);
  }
  return g;
}

/* ---------------- driver: sum over permutations ---------------- */
static int n, nthreads;
static int E[NMAX][NMAX];
static double Pd[NMAX][NMAX], Cd[NMAX];
static dd Px[NMAX][NMAX], Cx[NMAX];
static int emin, erange;
static int use_dd;

struct job_t { int first; std::vector<double> acc; };

static int next_perm(int *p,int len){
  int i=len-2; while(i>=0 && p[i]>p[i+1]) i--;
  if(i<0) return 0;
  int j=len-1; while(p[j]<p[i]) j--;
  int t=p[i]; p[i]=p[j]; p[j]=t;
  for(int a=i+1,b=len-1;a<b;a++,b--){ t=p[a]; p[a]=p[b]; p[b]=t; }
  return 1;
}

template<class R> static void work_t(job_t *jb){
  int p[NMAX], rest[NMAX], r=0;
  for(int i=0;i<n;i++) if(i!=jb->first) rest[r++]=i;
  R a[NMAX*NMAX], c[NMAX];
  do{
    p[0]=jb->first; for(int i=0;i<r;i++) p[i+1]=rest[i];
    int e=0;
    for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) e+=E[p[i]][p[j]];
    for(int i=0;i<n;i++){
      if constexpr (std::is_same<R,dd>::value){ c[i]=Cx[p[i]]; for(int j=0;j<n;j++) a[i*n+j]=Px[p[i]][p[j]]; }
      else { c[i]=Cd[p[i]]; for(int j=0;j<n;j++) a[i*n+j]=Pd[p[i]][p[j]]; }
    }
    double f=F(a,c,n);
    if(f!=0) jb->acc[e-emin]+=f;
  } while(next_perm(rest,r));
}
static void *work(void *arg){
  job_t *jb=(job_t*)arg;
  if(use_dd) work_t<dd>(jb); else work_t<double>(jb);
  return NULL;
}

static std::vector<double> run_all(){
  std::vector<job_t> jobs(n);
  pthread_t th[NMAX];
  for(int f=0;f<n;f++){ jobs[f].first=f; jobs[f].acc.assign(erange,0.0); }
  int nt = nthreads<1 ? 1 : nthreads;
  for(int f0=0;f0<n;f0+=nt){
    int f1=f0+nt; if(f1>n) f1=n;
    if(f1-f0==1) work(&jobs[f0]);
    else {
      for(int f=f0;f<f1;f++) pthread_create(&th[f],NULL,work,&jobs[f]);
      for(int f=f0;f<f1;f++) pthread_join(th[f],NULL);
    }
  }
  std::vector<double> tot(erange,0.0);
  for(int f=0;f<n;f++) for(int e=0;e<erange;e++) tot[e]+=jobs[f].acc[e];
  return tot;
}

static int solve_one(void){
  if(scanf("%d %d %d",&n,&nthreads,&noloop)!=3) return 0;
  if(n<1||n>NMAX) { fprintf(stderr,"n out of range\n"); return 0; }
  char buf[256];
  for(int i=0;i<n;i++) for(int j=0;j<n;j++) if(scanf("%d",&E[i][j])!=1) return 0;
  for(int i=0;i<n;i++) for(int j=0;j<n;j++){ if(scanf("%255s",buf)!=1) return 0; parse_num(buf,&Pd[i][j],&Px[i][j]); }
  for(int i=0;i<n;i++){ if(scanf("%255s",buf)!=1) return 0; parse_num(buf,&Cd[i],&Cx[i]); }
  if(n==1){ printf("0 1\nEND\n"); fflush(stdout); return 1; }
  int tot=0; for(int i=0;i<n;i++) for(int j=0;j<n;j++) tot+=abs(E[i][j]);
  emin=-tot; erange=2*tot+1;
  ambiguous=0; ddzeros=0; use_dd=0;
  static int force_dd = getenv("COULOMBIDX_DD")!=NULL;
  std::vector<double> res;
  if(!force_dd) res=run_all(); else ambiguous=1;
  if(ambiguous>0){ ambiguous=0; use_dd=1; res=run_all(); printf("DOUBLEDOUBLE\n");
    if(ddzeros>0) printf("DDZEROS %ld\n",(long)ddzeros); }
  for(int e=0;e<erange;e++) if(res[e]!=0) printf("%d %.17g\n",e+emin,res[e]);
  if(ambiguous>0) printf("AMBIGUOUS %ld\n",(long)ambiguous);
  printf("END\n"); fflush(stdout);
  return 1;
}

int main(void){
  while(solve_one()) ;
  return 0;
}
