/* twsim TBL MAXSTEPS MAXBEEPS: prints "step ones" at each visit of the beep state. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef struct { int w, m, n; } Tr;
int main(int c, char **v) {
  FILE *f = fopen(v[1], "r"); long long ms = atoll(v[2]), mb = atoll(v[3]);
  int ns, beep; if (fscanf(f, "%d %d", &ns, &beep) != 2) return 2;
  Tr *t = malloc(sizeof(Tr) * 2 * ns);
  for (int i = 0; i < 2 * ns; i++) if (fscanf(f, "%d %d %d", &t[i].w, &t[i].m, &t[i].n) != 3) return 2;
  size_t cap = 1 << 22; uint8_t *tp = calloc(cap, 1); size_t h = cap / 2, lo = h, hi = h;
  int s = 0; long long nb = 0;
  for (long long st = 0; st < ms; st++) {
    if (s == beep) {
      long long o = 0; for (size_t i = lo; i <= hi; i++) o += tp[i];
      printf("%lld %lld\n", st, o); fflush(stdout); if (++nb >= mb) return 0;
    }
    Tr *r = &t[2 * s + tp[h]];
    if (r->n < 0) { printf("HALT %lld %d\n", st, s); return 1; }
    tp[h] = r->w; h += r->m ? 1 : -1; s = r->n;
    if (h < lo) lo = h; if (h > hi) hi = h;
    if (h == 0 || h == cap - 1) { printf("TAPE\n"); return 3; }
  }
  return 0;
}
