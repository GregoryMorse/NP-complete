/* Counter-machine interpreter (for long differential runs).
 * usage: cmsim PROG.cm MAX_STEPS MAX_BEEPS
 * PROG.cm: "ninstr nregs entry jreg sreg" then per instruction
 *   0 r nxt        INC
 *   1 r nz z       DEC
 *   2 nxt          BEEP
 * prints "step J S" per beep; at the end "steps N beeps B" on stderr.
 */
#include <stdio.h>
#include <stdlib.h>
typedef struct { int op, r, a, b; } I;
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r");
    long long maxs = atoll(argv[2]), maxb = atoll(argv[3]);
    int n, nr, pc, jr, sr;
    if (fscanf(f, "%d %d %d %d %d", &n, &nr, &pc, &jr, &sr) != 5) return 2;
    I *p = calloc(n, sizeof(I));
    for (int i = 0; i < n; i++) {
        if (fscanf(f, "%d", &p[i].op) != 1) return 2;
        if (p[i].op == 0) { if (fscanf(f, "%d %d", &p[i].r, &p[i].a) != 2) return 2; }
        else if (p[i].op == 1) { if (fscanf(f, "%d %d %d", &p[i].r, &p[i].a, &p[i].b) != 3) return 2; }
        else { if (fscanf(f, "%d", &p[i].a) != 1) return 2; }
    }
    unsigned long long *R = calloc(nr, sizeof *R);
    long long s = 0, beeps = 0;
    for (; s < maxs; s++) {
        I *x = &p[pc];
        if (x->op == 0) { R[x->r]++; pc = x->a; }
        else if (x->op == 1) { if (R[x->r]) { R[x->r]--; pc = x->a; } else pc = x->b; }
        else { pc = x->a; printf("%lld %llu %llu\n", s, R[jr], R[sr]);
               if (++beeps >= maxb) { s++; break; } }
    }
    fprintf(stderr, "steps %lld beeps %lld\n", s, beeps);
    return 0;
}
