/* 2-symbol TM simulator for the native machines.
 * usage: psim MACHINE.tbl MAX_STEPS MAX_BEEPS
 * At every beep prints "step lo bits": the tape from cell lo (first nonzero)
 * to the last nonzero cell, cells relative to the start position.
 * Exit status 3 if an undefined transition is met. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct { int w, m, n; } Tr;
int main(int argc, char **argv) {
    if (argc < 4) return 2;
    FILE *f = fopen(argv[1], "r");
    long long maxsteps = atoll(argv[2]), maxbeeps = atoll(argv[3]);
    int ns, beep;
    if (fscanf(f, "%d %d", &ns, &beep) != 2) return 2;
    Tr *t = malloc(sizeof(Tr) * 2 * ns);
    for (int i = 0; i < 2 * ns; i++)
        if (fscanf(f, "%d %d %d", &t[i].w, &t[i].m, &t[i].n) != 3) return 2;
    long long cap = 1 << 20, off = cap / 2;
    unsigned char *tape = calloc(cap, 1);
    long long h = off, lo = off, hi = off;
    int s = 0;
    long long beeps = 0;
    for (long long step = 0; step < maxsteps; step++) {
        if (h <= 0 || h >= cap - 1) {
            long long nc = cap * 2, sh = cap / 2;
            unsigned char *nt = calloc(nc, 1);
            memcpy(nt + sh, tape, cap);
            free(tape); tape = nt; cap = nc; h += sh; off += sh; lo += sh; hi += sh;
        }
        Tr *tr = &t[2 * s + tape[h]];
        if (tr->n < 0) { printf("UNDEF %lld %d %d\n", step, s, tape[h]); return 3; }
        tape[h] = tr->w;
        if (tr->w) { if (h < lo) lo = h; if (h > hi) hi = h; }
        h += tr->m ? 1 : -1;
        s = tr->n;
        if (s == beep) {
            long long a = lo, b = hi;
            while (a <= b && !tape[a]) a++;
            while (b >= a && !tape[b]) b--;
            printf("%lld %lld ", step, a - off);
            for (long long i = a; i <= b; i++) putchar('0' + tape[i]);
            putchar('\n');
            if (++beeps >= maxbeeps) return 0;
        }
    }
    printf("STEPS\n");
    return 0;
}
