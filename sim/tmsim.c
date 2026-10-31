/* Fast 2-symbol TM simulator with beep reporting.
 *
 * usage: tmsim MACHINE.tbl MAX_STEPS MAX_BEEPS NREGS
 * MACHINE.tbl:  first line "nstates beepstate", then one line per state
 *               "w0 m0 n0 w1 m1 n1" (m: 0 = L, 1 = R; n = -1 undefined).
 * For every beep prints:  step  r_0 ... r_{NREGS-1}
 * (registers decoded from the unary block layout, head on the last data cell).
 * Values larger than the tape are not a concern: the tape grows on demand.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef struct { int w, m, n; } Tr;

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage\n"); return 2; }
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror("open"); return 2; }
    long long maxsteps = atoll(argv[2]);
    long long maxbeeps = atoll(argv[3]);
    int nregs = atoi(argv[4]);
    int ns, beep;
    if (fscanf(f, "%d %d", &ns, &beep) != 2) return 2;
    Tr *t = malloc(sizeof(Tr) * 2 * ns);
    for (int i = 0; i < ns; i++)
        for (int a = 0; a < 2; a++)
            if (fscanf(f, "%d %d %d", &t[2*i+a].w, &t[2*i+a].m, &t[2*i+a].n) != 3) return 2;
    fclose(f);
    size_t cap = 1 << 20;
    uint8_t *tape = calloc(cap, 1);
    size_t h = cap / 2;
    int s = 0;
    long long beeps = 0, step = 0;
    while (step < maxsteps) {
        Tr *tr = &t[2*s + tape[h]];
        if (tr->n < 0) { printf("HALT %lld state %d\n", step, s); return 1; }
        tape[h] = (uint8_t)tr->w;
        if (tr->m) h++; else h--;
        s = tr->n;
        step++;
        if (h == 0 || h == cap - 1) {           /* grow both ways */
            size_t ncap = cap * 2;
            uint8_t *nt = calloc(ncap, 1);
            memcpy(nt + cap / 2, tape, cap);
            free(tape);
            tape = nt; h += cap / 2; cap = ncap;
        }
        if (s == beep) {
            printf("%lld", step);
            long p = (long)h;                     /* last data cell */
            long long *v = malloc(sizeof(long long) * nregs);
            for (int r = nregs - 1; r >= 0; r--) {
                long long c = 0;
                while (p >= 0 && tape[p] == 1) { c++; p--; }
                v[r] = c - 1; p--;
            }
            for (int r = 0; r < nregs; r++) printf(" %lld", v[r]);
            printf("\n");
            free(v);
            fflush(stdout);
            if (++beeps >= maxbeeps) break;
        }
    }
    fprintf(stderr, "steps %lld beeps %lld\n", step, beeps);
    return 0;
}
