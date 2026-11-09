"""Twin-prime beeper, hand design (see README.md).

Tape (blank elsewhere):   D 0 R
  D : d cells, all 1 except one hole (0) at cell c, a counter mod d
  0 : the separator
  R : r = m - d cells, all 1 except, during the walk, one hole moving right
Candidate m >= 3 (lesser twin test of m, m+2), divisor d = 2 .. m-1.
"""
# state: (on 0, on 1); each action (write, move, next) or None (never used)
T = {
    # --- rebuild: one block of m+1 ones -> candidate m+1 with d = 2 ---------
    'C4': ((1, 'R', 'C5'), (1, 'L', 'C4')),   # start state: run left to the blank, add a 1
    'C5': ((1, 'R', 'C1'), (0, 'R', 'G1')),   # D = 1 0 (hole on its last cell); 0: start only
    'C1': ((1, 'L', 'C4'), (1, 'R', 'C1')),   # fill the separator, back to the left end
    # --- shift: d += 1, r -= 1 -----------------------------------------------
    'G1': (None,           (0, 'R', 'G2')),   # R's cell 0 becomes the separator
    'G2': ((0, 'L', 'BP'), (0, 'L', 'Y1')),   # R empty: every d passed -> beep; else first R hole
    'BP': ((0, 'L', 'X1'), None),             # BEEP state (only entered from G2 on 0)
    # --- walk ----------------------------------------------------------------
    'B':  ((0, 'L', 'V'),  (0, 'L', 'Y1')),   # next R cell becomes the R hole; blank: walk over
    'Y1': ((0, 'L', 'Y2'), (1, 'L', 'Y1')),   # left past the separator
    'Y2': ((1, 'R', 'A'),  (1, 'L', 'Y2')),   # left to D's hole, fill it
    'A':  ((0, 'L', 'W'),  (0, 'R', 'Z1')),   # new D hole one cell right; separator: wrap
    'W':  ((0, 'R', 'A'),  (1, 'L', 'W')),    # wrap: to D's left end
    'Z1': ((0, 'R', 'Z2'), (1, 'R', 'Z1')),   # right past the separator
    'Z2': ((1, 'R', 'B'),  (1, 'R', 'Z2')),   # right to R's hole, fill it
    # --- check: D's hole c = (m-1) mod d; fail iff c in {d-1, d-3} -----------
    'V':  ((0, 'L', 'X1'), (1, 'L', 'V')),    # back to the separator
    'X1': ((1, 'R', 'C1'), (1, 'L', 'X2')),   # c = d-1: d | m        -> fail
    'X2': ((1, 'R', 'H1'), (1, 'L', 'X3')),   # c = d-2               -> pass
    'X3': ((1, 'R', 'C1'), (1, 'L', 'H0')),   # c = d-3: d | m+2      -> fail
    'H0': ((1, 'R', 'H1'), (1, 'L', 'H0')),   # c < d-3: fill the hole -> pass
    'H1': ((0, 'R', 'G1'), (1, 'R', 'H1')),   # to the separator (it stays: D's new last cell, the hole)
}
START, BEEP = 'C4', 'BP'
ORDER = list(T)  # START first


def run(T, start, beep, steps, maxbeeps=None):
    tape, h, q, beeps = {}, 0, start, []
    for n in range(steps):
        if q == beep:
            beeps.append((n, dict(tape)))
            if maxbeeps and len(beeps) >= maxbeeps:
                break
        a = tape.get(h, 0)
        act = T[q][a]
        if act is None:
            raise RuntimeError(f'undefined {q},{a} at step {n}')
        w, mv, q = act
        tape[h] = w
        h += 1 if mv == 'R' else -1
    return beeps


def lesser_twins(k):
    P = lambda n: n > 1 and all(n % d for d in range(2, int(n**.5) + 1))
    out, m = [], 3
    while len(out) < k:
        if P(m) and P(m + 2):
            out.append(m)
        m += 1
    return out


def ones_block(tape):
    return sum(tape.values())


if __name__ == '__main__':
    import sys
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    bs = run(T, START, BEEP, 10**9, k)
    got = [ones_block(t) for _, t in bs]  # at a beep: D has m-1 ones (hole = old separator), R gone
    print('steps', [n for n, _ in bs])
    print('m from tape', [g + 1 for g in got])
    print('twins      ', lesser_twins(k))
