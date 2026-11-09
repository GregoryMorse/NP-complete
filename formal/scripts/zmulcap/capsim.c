/* capsim TABLE MAXSTEPS GC DP30 DP31 LL0 LL1 TAPE HEAD FBACK  (driver: run.py)
 * prints: OUT o steps minslack npops   (minslack = -1: a deposit had no non-blank to its left: overflow) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct { int w, m, n; } Tr;
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r"); int ns; if (fscanf(f, "%d", &ns) != 1) return 2;
  Tr *t = malloc(sizeof(Tr) * 4 * ns);
  for (int i = 0; i < 4 * ns; i++) if (fscanf(f, "%d %d %d", &t[i].w, &t[i].m, &t[i].n) != 3) return 2;
  long long maxsteps = atoll(argv[2]); int s = atoi(argv[3]), d0 = atoi(argv[4]), d1 = atoi(argv[5]);
  int ll0 = atoi(argv[6]), ll1 = atoi(argv[7]);
  long long cap = 1 << 24; unsigned char *tp = calloc(cap, 1); long long base = cap / 2, lo;
  const char *init = argv[8];
  for (size_t i = 0; i < strlen(init); i++) tp[base + i] = strchr("BM01", init[i]) - "BM01";
  long long h = base + atoll(argv[9]); lo = base;
  long long minsl = 1LL << 60, np = 0;
  int fb = atoi(argv[10]); long long lastrho = -1, rhodec = 0, minrho = 1LL<<60; int prev = -1;
  for (long long st = 0; st < maxsteps; st++) {
    if (s == fb && prev != fb) { long long p = lo - 2; while (tp[p] == 0) p++; while (tp[p] >= 2) p++;
      long long e = p; while (tp[p] != 1) p++;
      long long rho = p - e; if (lastrho >= 0 && rho < lastrho) rhodec++; lastrho = rho; if (rho < minrho) minrho = rho; }
    prev = s;
    if (h <= 1 || h >= cap - 2) { printf("TAPE\n"); return 0; }
    if (h < lo) lo = h;
    if (s == d0 || s == d1) { printf("OUT %d %lld %lld %lld %lld %lld\n", s == d1, st, minsl == (1LL<<60) ? 99999 : minsl, np, rhodec, minrho); return 0; }
    if ((s == ll0 || s == ll1) && tp[h] == 0) {
      long long k = 1; while (h - k >= lo - 2 && tp[h - k] == 0) k++;
      long long sl = (h - k < lo - 2) ? -1 : k - 1; np++;
      if (sl < minsl) minsl = sl;
    }
    Tr *r = &t[4 * s + tp[h]];
    if (r->n < 0) { printf("UNDEF %d %d %lld\n", s, tp[h], st); return 0; }
    tp[h] = r->w; h += r->m ? 1 : -1; s = r->n;
  }
  printf("STEPS\n"); return 0;
}
