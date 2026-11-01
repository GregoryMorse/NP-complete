/* Logical (4-symbol) machine instance runner.
 * usage: lsim TABLE MAXSTEPS START_STATE OK_STATE BAD_STATE TAPE HEAD
 * TABLE: "ns" then ns*4 lines "w m n" (n=-1 undefined), symbols B M 0 1 = 0..3.
 * Prints OK / BAD / STEPS / UNDEF q a. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct { int w, m, n; } Tr;
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int ns;
    if (fscanf(f, "%d", &ns) != 1) return 2;
    Tr *t = malloc(sizeof(Tr) * 4 * ns);
    for (int i = 0; i < 4 * ns; i++) if (fscanf(f, "%d %d %d", &t[i].w, &t[i].m, &t[i].n) != 3) return 2;
    long long maxsteps = atoll(argv[2]); int s = atoi(argv[3]), ok = atoi(argv[4]), bad = atoi(argv[5]);
    long long cap = 1 << 22, h; unsigned char *tape = calloc(cap, 1);
    const char *init = argv[6]; long long base = cap / 2;
    for (size_t i = 0; i < strlen(init); i++) tape[base + i] = strchr("BM01", init[i]) - "BM01";
    h = base + atoll(argv[7]);
    for (long long step = 0; step < maxsteps; step++) {
        if (h <= 0 || h >= cap - 1) {
            long long nc = cap * 2, sh = cap / 2; unsigned char *nt = calloc(nc, 1);
            memcpy(nt + sh, tape, cap); free(tape); tape = nt; cap = nc; h += sh;
        }
        Tr *tr = &t[4 * s + tape[h]];
        if (tr->n < 0) { printf("UNDEF %d %d %lld\n", s, tape[h], step); return 0; }
        tape[h] = tr->w; h += tr->m ? 1 : -1; s = tr->n;
        if (s == ok) { printf("OK %lld\n", step); return 0; }
        if (s == bad) { printf("BAD %lld\n", step); return 0; }
    }
    printf("STEPS\n"); return 0;
}
