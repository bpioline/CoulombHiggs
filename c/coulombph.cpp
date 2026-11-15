/* coulombph.cpp -- Coulomb index of n centres from a closed formula for the indexed number of
   collinear solutions in each ordering (Poincare-Hopf on the compactified configuration space).

   For an ordering x_1<...<x_n of centres with DSZ products a_ij and FI terms c_i, the indexed
   number of critical points of W = -sum_{i<j} a_ij log(x_j-x_i) - sum_i c_i x_i (modulo
   translations) is
        F = sum over laminar families S of "inward" facets of (-1)^{|S|},
   where the facets of the compactified domain (an associahedron on the n+1 letters
   1,...,n,infinity) are the intervals [i,j] of letters with 2 <= j-i+1 <= n:
     - [i,j] with j<=n  (centres i..j collide):     inward iff S_ij = sum_{i<=a<b<=j} a_ab < 0
     - [k+1,n+1]        (gap k goes to infinity):    inward iff c_1+...+c_k < 0
   and a family is laminar if any two of its intervals are nested or disjoint.  The sum is
   evaluated by an interval recursion while the orderings are enumerated depth first.

   Input/output: identical to coulombidx (see coulombidx.cpp): problems "n nthreads noloop",
   E (n x n integers), P (n x n rationals p/q), c (n rationals); output lines "e v", END.
   All sign tests are exact (128-bit integers after clearing denominators).  If a tested quantity
   vanishes exactly, or the input cannot be represented exactly, the problem is flagged
   "AMBIGUOUS k" and the caller falls back to the exact Mathematica recursion.  noloop=1 is
   not supported (flagged AMBIGUOUS).
   Build: c++ -O3 -std=c++17 -o coulombph coulombph.cpp -lpthread                          */

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <atomic>
#include <vector>
#include <pthread.h>

#define NMAX 16
typedef long long ll;
typedef __int128 i128;

static int n, nthreads, noloop;
static int E[NMAX][NMAX];
static i128 P[NMAX][NMAX], C[NMAX];      /* numerators over common denominators (128-bit) */
static int emin, erange;
static std::atomic<long> zeros(0);
static int bad_input;

static ll gcdll(ll a, ll b){ if(a<0) a=-a; if(b<0) b=-b; while(b){ ll t=a%b; a=b; b=t; } return a; }

/* parse "p/q" or an integer; decimals are rejected (bad_input) */
static int parse_rat(const char *s, ll *p, ll *q){
  const char *sl = strchr(s,'/');
  char *end;
  if(strpbrk(s,".eE")) return 0;
  *p = strtoll(s,&end,10);
  if(sl){ *q = strtoll(sl+1,&end,10); if(*q<=0) return 0; } else *q = 1;
  return 1;
}

/* bring a list of rationals to a common denominator; returns 0 on overflow */
static int common(int m, ll *num, ll *den, i128 *out){
  i128 L = 1;
  for(int i=0;i<m;i++){ ll g = gcdll((ll)L, den[i]); L = L/g*den[i]; if(L > ((i128)1<<62)) return 0; }
  for(int i=0;i<m;i++){ i128 v = (i128)num[i]*(L/den[i]); if(v > ((i128)1<<100) || v < -((i128)1<<100)) return 0; out[i]=v; }
  return 1;
}

struct job_t { int a, b; std::vector<ll> acc; long zeros; };

/* depth-first enumeration below a fixed prefix */
struct Walker {
  int p[NMAX+1];              /* p[1..j] centres in positions 1..j */
  int used[NMAX];
  i128 S[NMAX+2][NMAX+2];      /* S[i][j] = sum_{i<=a<b<=j} P[p_a][p_b] */
  ll  dseq[NMAX+2][NMAX+2];   /* dseq[i][t]: laminar families inside [i,t] */
  ll  inner[NMAX+2][NMAX+2];  /* inner[i][j]: families of proper subintervals of [i,j] */
  int w[NMAX+2][NMAX+2];      /* -1 if facet [i,j] is inward, 0 otherwise */
  i128 ctil[NMAX+1];           /* ctil[k] = C[p_1]+...+C[p_k] */
  int ex[NMAX+1];             /* y-exponent of the prefix */
  long nzero;
  ll *acc;

  void push(int j){           /* position j has just been filled with p[j] */
    int cj = p[j];
    i128 T = 0;
    ex[j] = ex[j-1]; for(int l=1;l<j;l++) ex[j] += E[p[l]][cj];
    ctil[j] = ctil[j-1] + C[cj];
    for(int i=j-1;i>=1;i--){
      T += P[p[i]][cj];
      S[i][j] = S[i][j-1] + T;
      if(S[i][j]==0) nzero++;
      w[i][j] = S[i][j] < 0 ? -1 : 0;
    }
    inner[j][j] = 1; dseq[j][j] = 1;
    for(int i=j-1;i>=1;i--){
      ll v = dseq[i][j-1];
      for(int s=i+1;s<j;s++) if(w[s][j]) v -= dseq[i][s-1]*inner[s][j];
      inner[i][j] = v;
      dseq[i][j] = v + w[i][j]*v;
    }
  }
  ll leaf(){                  /* add the letter infinity at position n+1 */
    static thread_local ll inf[NMAX+2];
    int N = n+1;
    int wi[NMAX+2];
    for(int s=2;s<=n;s++){ i128 c = ctil[s-1]; if(c==0) nzero++; wi[s] = c < 0 ? -1 : 0; }
    inf[N] = 1;
    for(int i=n;i>=1;i--){
      ll v = dseq[i][n];
      for(int s=(i+1>2?i+1:2);s<=n;s++) if(wi[s]) v -= (i<=s-1 ? dseq[i][s-1] : 1)*inf[s];
      inf[i] = v;
    }
    return inf[1];
  }
  void rec(int j){            /* positions 1..j filled */
    if(j==n){ ll f = leaf(); if(f) acc[ex[n]-emin] += f; return; }
    for(int c=0;c<n;c++) if(!used[c]){
      used[c]=1; p[j+1]=c; push(j+1); rec(j+1); used[c]=0;
    }
  }
};

static void *work(void *arg){
  job_t *jb = (job_t*)arg;
  Walker *W = new Walker();
  memset(W->used,0,sizeof(W->used));
  W->ex[0]=0; W->ctil[0]=0; W->nzero=0; W->acc = jb->acc.data();
  W->p[1]=jb->a; W->used[jb->a]=1; W->push(1);
  if(n==1){ /* not used */ }
  W->p[2]=jb->b; W->used[jb->b]=1; W->push(2);
  W->rec(2);
  jb->zeros = W->nzero;
  delete W;
  return NULL;
}

static std::vector<ll> run_all(){
  std::vector<job_t> jobs;
  for(int a=0;a<n;a++) for(int b=0;b<n;b++) if(a!=b){ job_t j; j.a=a; j.b=b; j.acc.assign(erange,0); j.zeros=0; jobs.push_back(j); }
  int nt = nthreads<1 ? 1 : (nthreads>64 ? 64 : nthreads);
  std::atomic<int> next(0);
  struct ctx_t { std::vector<job_t> *jobs; std::atomic<int> *next; };
  ctx_t ctx{&jobs,&next};
  auto runner = [](void *a)->void*{
    ctx_t *c=(ctx_t*)a; int k;
    while((k = c->next->fetch_add(1)) < (int)c->jobs->size()) work(&(*c->jobs)[k]);
    return NULL; };
  std::vector<pthread_t> th(nt);
  if(nt==1) runner(&ctx);
  else { for(int t=0;t<nt;t++) pthread_create(&th[t],NULL,runner,&ctx); for(int t=0;t<nt;t++) pthread_join(th[t],NULL); }
  std::vector<ll> tot(erange,0);
  for(auto &j: jobs){ for(int e=0;e<erange;e++) tot[e]+=j.acc[e]; zeros += j.zeros; }
  return tot;
}

static int solve_one(void){
  if(scanf("%d %d %d",&n,&nthreads,&noloop)!=3) return 0;
  if(n<1||n>NMAX){ fprintf(stderr,"n out of range\n"); return 0; }
  char buf[256];
  static ll pn[NMAX*NMAX], pd[NMAX*NMAX], cn[NMAX], cd[NMAX];
  static i128 pv[NMAX*NMAX], cv[NMAX];
  bad_input = 0;
  for(int i=0;i<n;i++) for(int j=0;j<n;j++) if(scanf("%d",&E[i][j])!=1) return 0;
  for(int i=0;i<n*n;i++){ if(scanf("%255s",buf)!=1) return 0; if(!parse_rat(buf,&pn[i],&pd[i])) bad_input=1; }
  for(int i=0;i<n;i++){ if(scanf("%255s",buf)!=1) return 0; if(!parse_rat(buf,&cn[i],&cd[i])) bad_input=1; }
  if(n==1){ printf("0 1\nEND\n"); fflush(stdout); return 1; }
  if(!bad_input && !common(n*n,pn,pd,pv)) bad_input=1;
  if(!bad_input && !common(n,cn,cd,cv)) bad_input=1;
  if(bad_input || noloop){ printf("AMBIGUOUS 1\nEND\n"); fflush(stdout); return 1; }
  for(int i=0;i<n;i++){ C[i]=cv[i]; for(int j=0;j<n;j++) P[i][j]=pv[i*n+j]; }
  int tot=0; for(int i=0;i<n;i++) for(int j=0;j<n;j++) tot+=abs(E[i][j]);
  emin=-tot; erange=2*tot+1;
  zeros=0;
  std::vector<ll> res = run_all();
  for(int e=0;e<erange;e++) if(res[e]!=0) printf("%d %lld\n",e+emin,res[e]);
  if(zeros>0) printf("AMBIGUOUS %ld\n",(long)zeros);
  printf("END\n"); fflush(stdout);
  return 1;
}

int main(void){
  while(solve_one()) ;
  return 0;
}
