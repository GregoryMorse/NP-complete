/* Logical (4-symbol) machine event runner.
 * usage: esim TABLE MAXSTEPS START TAPE HEAD EVENTS MAXEV
 * TABLE as for lsim.  EVENTS: comma-separated state numbers.  Each time the
 * machine enters an event state from a different state, prints
 * "q step tape" (tape between the outermost non-blank cells, symbols BM01).
 * Stops after MAXEV events (prints END), at an undefined transition
 * (UNDEF q a step) or after MAXSTEPS (STEPS). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct { int w, m, n; } Tr;
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int ns;
    if (fscanf(f, "%d", &ns) != 1) return 2;
    Tr *t = malloc(sizeof(Tr) * 4 * ns);
    for (int i = 0; i < 4 * ns; i++) if (fscanf(f, "%d %d %d", &t[i].w, &t[i].m, &t[i].n) != 3) return 2;
    long long maxsteps = atoll(argv[2]); int s = atoi(argv[3]);
    char *ev = calloc(ns, 1);
    for (char *p = strtok(argv[6], ","); p; p = strtok(NULL, ",")) ev[atoi(p)] = 1;
    long long maxev = atoll(argv[7]), nev = 0;
    long long cap = 1 << 22, h, lo, hi; unsigned char *tape = calloc(cap, 1);
    const char *init = argv[4]; long long base = cap / 2;
    for (size_t i = 0; i < strlen(init); i++) tape[base + i] = strchr("BM01", init[i]) - "BM01";
    lo = base; hi = base + (long long)strlen(init);
    h = base + atoll(argv[5]);
    for (long long step = 0; step < maxsteps; step++) {
        if (h <= 0 || h >= cap - 1) {
            long long nc = cap * 2, sh = cap / 2; unsigned char *nt = calloc(nc, 1);
            memcpy(nt + sh, tape, cap); free(tape); tape = nt; cap = nc; h += sh; lo += sh; hi += sh;
        }
        Tr *tr = &t[4 * s + tape[h]];
        if (tr->n < 0) { printf("UNDEF %d %d %lld\n", s, tape[h], step); return 0; }
        tape[h] = tr->w; if (tr->w) { if (h < lo) lo = h; if (h >= hi) hi = h + 1; }
        h += tr->m ? 1 : -1;
        int prev = s; s = tr->n;
        if (ev[s] && s != prev) {
            long long a = lo, b = hi;
            while (a < b && !tape[a]) a++;
            while (b > a && !tape[b - 1]) b--;
            printf("%d %lld ", s, step);
            for (long long i = a; i < b; i++) putchar("BM01"[tape[i]]);
            putchar('\n');
            if (++nev >= maxev) { printf("END\n"); return 0; }
        }
    }
    printf("STEPS\n"); return 0;
}
