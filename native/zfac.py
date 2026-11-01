"""Native machine for FACTOR in P (reference: ref/zfac_ref.py).

Built from zp2 (Z_P v2).  The decider phase is unchanged; the verifier phase
(certificate counter, verifier runs) is replaced by a native brute-force
truth routine:

1. New instance: write M_2, walk to M_g and copy s to the left of M_g with the
   interpreter's own copy loop (GC).  The copy reads s reversed, left to right.
2. Conversion (Horner, in unary): consume the copy from its left end.  A pair
   '1b' doubles the current target block and adds b; a '0' opens a new target
   block.  Targets grow leftwards beyond a separator M:
       B .. n_3 M n_2 M n_1 M (consumed: blanks) .. M_g
   Doubling: the added bit is appended already marked ('0'), every unmarked '1'
   is marked and a marked cell appended, then all cells are unmarked.
3. Divisibility, K = n_1 (right), A = n_2 (left): for d = |K| down to 2 test
   d | |A| by marking A and K cell for cell (K is reset lazily when full);
   A is used up exactly when K is uniform.  A failed test shrinks K by one,
   turning its last cell into M.
4. Result o: erase the left side, then report o to the dispatch (DP1o), which
   writes the truth flag `M [1]` after M_2, then M_3 and the decider fuel.
"""
import zp2

B, M = 'B', 'M'
BITS = '01'
NB = '01M'


def build():
    m = zp2.build()
    drop = {'VA2', 'VA3', 'VA4', 'VN1', 'VN2', 'VU2', 'VFE', 'VF2', 'VG1', 'VG2', 'VG3',
            'BD1', 'BD2', 'BD3', 'BD4', 'BD5', 'BD6'}
    for k in [k for k in m.d if k[0] in drop or (k[0] in ('DP30', 'DP31') and k[1] in BITS)
              or k in (('GC', M), ('CX', B), ('SINC', '0'), ('JINC', '0'), ('SOV', B),
                       ('JOV2', B))]:
        del m.d[k]
    t = m.t
    # ---------------- new instance: M_2, then copy s left of M_g ----------------
    for f in ('SINC', 'JINC'):
        t(f, '0', '1', 'R', 'NI')
    t('SOV', B, '0', 'R', 'NI')
    t('JOV2', B, M, 'R', 'NI')
    t('NI', NB, '.', 'R', 'NI')
    t('NI', B, M, 'L', 'TL')                    # M_2; the slot after it stays blank
    t('TL', NB, '.', 'L', 'TL')
    t('TL', B, M, 'R', 'DG2')                   # H; DG2/DG3 -> GC copies s
    t('GC', M, '.', 'R', 'GP')                  # end of source: which phase?
    t('GP', M, '.', 'L', 'GCM')                 # decider flag: build Q as before
    t('GCM', M, B, 'L', 'GLM')
    t('GP', B, '.', 'L', 'TS')                  # blank slot: truth routine
    t('CX', B, '1', 'L', 'DW1')                 # every BLK is now decider fuel
    for o in BITS:
        t('ER2' + o, B, '.', 'R', 'ER2' + o)    # the truth routine leaves a gap
    # ---------------- conversion (copy consumed from its right end) ----------------
    t('TS', NB, '.', 'L', 'TS')
    t('TS', B, M, 'R', 'TS2')                   # separator of the first target
    t('TS2', BITS, '.', 'R', 'TS2')
    t('TS2', M, B, 'L', 'HPF')                  # H becomes the gap
    t('RW', NB, '.', 'R', 'RW')
    t('RW', B, '.', 'L', 'HPF')
    t('HPF', '1', B, 'L', 'HPD')
    t('HPF', '0', B, 'L', 'SW')
    t('HPF', M, '.', 'L', 'RS1')                # copy used up: last cell of K
    t('HPD', M, '.', 'L', 'RS1')                # trailing lone 1
    for x in '01M':
        q = 'SW' if x == M else 'CA' + x
        if x != M:
            t('HPD', x, B, 'L', q)
        t(q, NB, '.', 'L', q)
    t('CA1', B, '0', 'R', 'DR')                 # added bit, already marked
    t('CA0', B, '.', 'R', 'DR')
    t('SW', B, M, 'R', 'RW')                    # open the next target
    t('DR', '0', '.', 'R', 'DR')
    t('DR', '1', '0', 'L', 'DE')
    t('DR', M, '.', 'L', 'DU')
    t('DE', '0', '.', 'L', 'DE')
    t('DE', B, '0', 'R', 'DR')
    t('DU', '0', '1', 'L', 'DU')
    t('DU', B, '.', 'R', 'RW')
    # ---------------- divisibility loop ----------------
    # restore K to 1s right to left, checking |K| >= 2
    t('RS1', BITS, '1', 'L', 'RS2')
    t('RS2', BITS, '1', 'L', 'RS3')
    t('RS3', BITS, '1', 'L', 'RS3')
    t('RS3', M, '.', 'L', 'SA')
    for q in ('RS1', 'RS2'):
        t(q, 'MB', '.', 'R', 'FR0')
    t('RS3', B, '.', 'R', 'FR0')                # no second number
    t('SA', '0', '.', 'L', 'SA')
    t('SA', '1', '0', 'R', 'SK')
    t('SA', 'BM', '.', 'R', 'CHK')              # A used up
    t('SK', '0M', '.', 'R', 'SK')               # past A's marked cells into K
    t('SK', '1', '0', 'R', 'SK2')
    t('SK2', '1', '.', 'L', 'BACK')
    t('SK2', M, '.', 'L', 'RST')                # K full: reset it now
    t('RST', '0', '1', 'L', 'RST')
    t('RST', M, '.', 'L', 'SA')
    t('BACK', BITS, '.', 'L', 'BACK')
    t('BACK', M, '.', 'L', 'SA')
    t('CHK', '0', '1', 'R', 'CHK')              # restore A
    t('CHK', M, '.', 'R', 'KC')
    t('KC', '1', '.', 'R', 'KC')
    t('KC', M, '.', 'R', 'FR1')                 # K untouched: d divides a
    t('KC', '0', '.', 'R', 'ND')
    t('ND', BITS, '.', 'R', 'ND')
    t('ND', M, '.', 'L', 'SHR')
    t('SHR', BITS, M, 'L', 'RS1')               # d -= 1
    # ---------------- result: mark o in the gap, erase, report via ER1 ----------------
    for o in BITS:
        t('FR' + o, NB, '.', 'R', 'FR' + o)
        t('FR' + o, B, o, 'L', 'FE')
    t('FE', NB, B, 'L', 'FE')
    t('FE', B, '.', 'R', 'ER1')
    t('DP30', B, M, 'R', 'FB')                  # truth flag M, then M_3
    t('DP31', B, M, 'R', 'W1')
    t('W1', B, '1', 'R', 'FB')
    return m


if __name__ == '__main__':
    print(len(build().states()), 'logical states')
