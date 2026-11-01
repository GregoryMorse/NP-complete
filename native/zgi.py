"""Native machine for graph isomorphism in P (reference: ref/zgi_ref.py).

Built from zfac (native FACTOR): same new-instance glue and result path; the
binary conversion and the divisibility loop are replaced.

1. Setup: the copy of s (reversed) becomes a list of unary numbers (0 -> M)
   behind a boundary M:   B w_t M .. w_1 M M m M X .. MM H .. (gap)
2. Search: w is a stack of distinct values in 1..m, top at the left edge.
   Push a copy of m; while the top collides with another entry, decrement
   it; an emptied top is popped, and popping checks the stack below it (so
   every injective w is checked once).  Exhausted stack: reject.
3. Check w: for each edge (x, y) of X find a = w_x, b = w_y and the entry
   k = (a-1) m + b of H (entries are skipped by marking their first cell;
   the row part runs m times over the cells of a but its last), then delete
   the entry by marking its second cell (it must be an undeleted edge).
   Finally every edge of H must be deleted.  Failure unmarks everything.
4. Result o: erase the left side, then report o via ER1 (as in zfac).
"""
import zfac

B, M = 'B', 'M'
BITS = '01'
NB = '01M'
DROP = {'TS', 'TS2', 'RW', 'HPF', 'HPD', 'CA0', 'CA1', 'SW', 'DR', 'DE', 'DU',
        'RS1', 'RS2', 'RS3', 'SA', 'SK', 'SK2', 'RST', 'BACK', 'CHK', 'KC', 'ND', 'SHR'}


def build():
    m = zfac.build()
    for k in [k for k in m.d if k[0] in DROP]:
        del m.d[k]
    t = m.t
    F = 'gFG'                                   # candidate fails
    # ---------------- setup ----------------
    t('TS', NB, '.', 'L', 'TS')
    t('TS', B, M, 'R', 'gTC')                   # boundary M
    t('gTC', '1', '.', 'R', 'gTC')
    t('gTC', '0', M, 'R', 'gTC')
    t('gTC', M, B, 'L', 'gUP')                  # H becomes the gap
    # ---------------- push a copy of m (each entry is followed by its own M) ----------------
    t('gPR', '1', '.', 'R', 'gPR')
    t('gPR', M, '.', 'R', 'gPR2')
    t('gPR2', '1', '.', 'R', 'gPR')
    t('gPR2', M, '.', 'R', 'gPM')
    t('gPM', '0', '.', 'R', 'gPM')
    t('gPM', '1', '0', 'L', 'gPL')
    t('gPM', 'MB', '.', 'L', 'gPU')
    t('gPL', NB, '.', 'L', 'gPL')
    t('gPL', B, '1', 'R', 'gPR')
    t('gPU', '0', '1', 'L', 'gPU')
    t('gPU', '1M', '.', 'L', 'gPU')
    t('gPU', B, '.', 'R', 'gDP')
    # ---------------- collision of the top v with the other entries ----------------
    t('gKE', BITS, '.', 'R', 'gKE')
    t('gKE', M, '.', 'R', 'gKE1')
    t('gKE1', M, '.', 'L', 'gUP')               # boundary: no collision
    t('gKE1', '0', '.', 'R', 'gKE2')
    t('gKE1', '1', '0', 'R', 'gKP')
    t('gKE2', '0', '.', 'R', 'gKE2')
    t('gKE2', M, '.', 'R', 'gKE1')
    t('gKE2', '1', '0', 'R', 'gKP')
    t('gKP', '1', '.', 'L', 'gKBm')
    t('gKP', M, '.', 'L', 'gKBd')
    for x in 'md':
        t('gKB' + x, NB, '.', 'L', 'gKB' + x)
        t('gKB' + x, B, '.', 'R', 'gKV' + x)
        t('gKV' + x, '0', '.', 'R', 'gKV' + x)
        t('gKV' + x, '1', '0', 'R', 'gKQ' + x)
    t('gKQm', '1', '.', 'R', 'gKE')
    t('gKQm', M, '.', 'R', 'gKR1')              # v < e: mark the rest of e
    t('gKQd', '1', '.', 'L', 'gKUV')            # e < v
    t('gKQd', M, '.', 'R', F)                   # e = v
    t('gKR1', '0M', '.', 'R', 'gKR1')
    t('gKR1', '1', '0', 'R', 'gKR2')
    t('gKR2', '1', '0', 'R', 'gKR2')
    t('gKR2', M, '.', 'L', 'gKUV')
    t('gKUV', NB, '.', 'L', 'gKUV')
    t('gKUV', B, '.', 'R', 'gKU2')
    t('gKU2', '0', '1', 'R', 'gKU2')
    t('gKU2', '1', '.', 'R', 'gKU2')
    t('gKU2', M, '.', 'R', 'gKE1')
    t('gUP', '0', '1', 'L', 'gUP')
    t('gUP', '1M', '.', 'L', 'gUP')
    t('gUP', B, M, 'R', 'gPR2')                 # push
    # ---------------- decrement / pop ----------------
    t('gDC', '1', B, 'R', 'gDP')
    t('gDC', M, '.', 'R', 'FR0')                # empty stack: reject
    t('gDP', '1', '.', 'R', 'gKE')
    t('gDP', M, B, 'R', 'gGL')                  # top emptied: pop, check below
    # ---------------- check w: navigation ----------------
    t('gGL', NB, '.', 'L', 'gGL')
    t('gGL', B, '.', 'R', 'gUW2')
    t('gUW', '0', '1', 'R', 'gUW')              # unmark w, then m, on the way to X
    t('gUW', '1', '.', 'R', 'gUW')
    t('gUW', M, '.', 'R', 'gUW2')
    t('gUW2', '0', '1', 'R', 'gUW')
    t('gUW2', '1', '.', 'R', 'gUW')
    t('gUW2', M, '.', 'R', 'gXm')
    t('gCX', BITS, '.', 'R', 'gCX')
    t('gCX', M, '.', 'R', 'gCX2')
    t('gCX2', BITS, '.', 'R', 'gCX')
    t('gCX2', M, '.', 'R', 'gXm')
    t('gXm', '0', '1', 'R', 'gXm')
    t('gXm', '1', '.', 'R', 'gXm')
    t('gXm', M, '.', 'R', 'gY1e')
    t('gXm', B, '1', 'L', 'FE')                 # no X, no H: accept
    # current label of X: the first one not fully marked; parity e/o = first/second of its edge
    for p, q in (('e', 'o'), ('o', 'e')):
        t('gY1' + p, '0', '.', 'R', 'gY2' + p)
        t('gY2' + p, '0', '.', 'R', 'gY2' + p)
        t('gY2' + p, M, '.', 'R', 'gY1' + q)
        for y in ('gY1' + p, 'gY2' + p):
            t(y, '1', '0', 'R', 'gLP' + p)
        t('gLP' + p, '1', '.', 'L', 'gLW1')     # more cells: skip an entry of w
    t('gY1e', M, '.', 'R', 'gFN1')              # X done: final check
    t('gY1e', B, '1', 'L', 'FE')
    t('gY2o', B, '1', 'L', 'FE')
    t('gY1o', M, '.', 'R', F)                   # odd number of labels
    t('gY1o', B, '.', 'L', F)
    t('gY2e', B, '.', 'L', F)
    t('gLPe', 'MB', '.', 'L', 'gM1')            # a found: row part
    t('gLPo', 'MB', '.', 'L', 'gIL0')           # b found: column part
    # skip one entry of w (mark it fully)
    t('gLW1', NB, '.', 'L', 'gLW1')
    t('gLW1', B, '.', 'R', 'gLW2b')
    t('gLW2', '0', '.', 'R', 'gLW2')
    t('gLW2', M, '.', 'R', 'gLW2b')
    t('gLW2b', M, '.', 'R', F)                  # x > |w|
    t('gLW2b', '0', '.', 'R', 'gLW2')
    for q in ('gLW2', 'gLW2b'):
        t(q, '1', '0', 'R', 'gLW3')
    t('gLW3', '1', '0', 'R', 'gLW3')
    t('gLW3', M, '.', 'R', 'gCX2')
    # row part: mark the last cell of m (marks grow leftwards), then the inner loop
    t('gM1', '0M', '.', 'L', 'gM1')
    t('gM1', '1', '0', 'L', 'gTR1')
    t('gM1', B, '.', 'R', F)
    # inner loop: one entry of H per cell of the target but its last
    t('gIL0', NB, '.', 'L', 'gIL0')
    t('gIL0', B, '.', 'R', 'gIL1b')
    t('gIL1', '0', '.', 'R', 'gIL1')
    t('gIL1', M, '.', 'R', 'gIL1b')
    t('gIL1b', M, '.', 'R', F)                  # no target
    t('gIL1b', '0', '.', 'R', 'gIL1')
    for q in ('gIL1', 'gIL1b'):
        t(q, '1', '0', 'R', 'gILp')
    t('gILp', '1', '.', 'R', 'gN1')
    t('gILp', M, '.', 'L', 'gILu')
    t('gILu', '0', '1', 'R', 'gD1')
    t('gN1', BITS, '.', 'R', 'gN1')
    t('gN1', M, '.', 'R', 'gN1b')
    t('gN1b', BITS, '.', 'R', 'gN1')
    t('gN1b', M, '.', 'R', 'gN2')
    t('gN2', BITS, '.', 'R', 'gN2')
    t('gN2', M, '.', 'R', 'gN2b')
    t('gN2b', BITS, '.', 'R', 'gN2')
    t('gN2b', M, '.', 'R', 'gS3')
    for q in ('gN2', 'gN2b'):
        t(q, B, '.', 'L', F)
    t('gS3', '0', '.', 'R', 'gS4')              # first entry not yet passed
    t('gS3', '1', '0', 'L', 'gIL0')
    t('gS3', M, '.', 'R', F)
    t('gS3', B, '.', 'L', F)
    t('gS4', BITS, '.', 'R', 'gS4')
    t('gS4', M, '.', 'R', 'gS3')
    t('gS4', B, '.', 'L', F)
    # inner loop done: marks in m = row part (next cell of m), none = column part done
    t('gD1', BITS, '.', 'R', 'gD1')
    t('gD1', M, '.', 'R', 'gD1b')
    t('gD1b', BITS, '.', 'R', 'gD1')
    t('gD1b', M, '.', 'R', 'gD2')
    t('gD2', '1', '.', 'R', 'gD2')
    t('gD2', '0', '.', 'L', 'gD3')
    t('gD2', M, '.', 'R', 'gN2c')
    t('gD3', '1', '0', 'L', 'gTR1')
    t('gD3', M, '.', 'L', 'gGL')                # row part done: unmark w, m; on to b
    # reset the target (unmark all but its last cell), rerun the inner loop
    t('gTR1', NB, '.', 'L', 'gTR1')
    t('gTR1', B, '.', 'R', 'gTR2b')
    t('gTR2', '0', '.', 'R', 'gTR2')
    t('gTR2', M, '.', 'R', 'gTR2b')
    t('gTR2b', M, '.', 'R', F)
    t('gTR2b', '0', '.', 'R', 'gTR2')
    for q in ('gTR2', 'gTR2b'):
        t(q, '1', '.', 'L', 'gTR3')
    t('gTR3', '0', '1', 'L', 'gTR3')
    t('gTR3', M, '.', 'R', 'gIL1')
    t('gTR3', B, '.', 'R', 'gIL1')
    # column part done: unmark the passed entries; the first unpassed one is k
    t('gN2c', BITS, '.', 'R', 'gN2c')
    t('gN2c', M, '.', 'R', 'gN2d')
    t('gN2d', BITS, '.', 'R', 'gN2c')
    t('gN2d', M, '.', 'R', 'gHU')
    for q in ('gN2c', 'gN2d'):
        t(q, B, '.', 'L', F)
    t('gHU', '0', '1', 'R', 'gHU2')
    t('gHU', '1', '.', 'R', 'gHC')
    t('gHU', M, '.', 'R', F)
    t('gHU', B, '.', 'L', F)
    t('gHU2', BITS, '.', 'R', 'gHU2')
    t('gHU2', M, '.', 'R', 'gHU')
    t('gHU2', B, '.', 'L', F)
    t('gHC', '1', '0', 'L', 'gGL')              # delete edge k; next edge
    t('gHC', '0M', '.', 'R', F)
    t('gHC', B, '.', 'L', F)
    # final check: every edge of H deleted
    t('gFN1', '1', '.', 'R', 'gFN2')
    t('gFN1', M, '.', 'R', 'FR1')
    t('gFN1', B, '1', 'L', 'FE')
    t('gFN2', '1', '.', 'R', F)
    t('gFN2', '0', '.', 'R', 'gFN3')
    t('gFN2', M, '.', 'R', 'gFN1')
    t('gFN2', B, '1', 'L', 'FE')
    t('gFN3', BITS, '.', 'R', 'gFN3')
    t('gFN3', M, '.', 'R', 'gFN1')
    t('gFN3', B, '1', 'L', 'FE')
    # failure: unmark everything, decrement the top
    t(F, NB, '.', 'R', F)
    t(F, B, '.', 'L', 'gFL')
    t('gFL', '0', '1', 'L', 'gFL')
    t('gFL', '1M', '.', 'L', 'gFL')
    t('gFL', B, '.', 'R', 'gDC')
    return m


if __name__ == '__main__':
    print(len(build().states()), 'logical states')
