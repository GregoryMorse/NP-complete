"""Native machine for the GF(2) matrix product in linear time (reference: ref/zmm_ref.py).

Z_MUL (native/zmul.py) with a new output check.  The guest model, the switch,
the fuel, the copy of s next to out and the dispatch are zmul's; H stays M.

Check layout (logical direction F = physical left, away from M_g):

    M_g out Ms [acc with the hole H] Mr [B rows with the hole P] M [A] s-end

* s = 1^m 0 w: B = the first m^2 cells of w, A = the rest (rows of m, the
  last padded with 0s), row-major; C = A B over GF(2) (ref/zmm_ref.py).
* out = c_0 c_1 ..; consumed cells become blank (from the M_g side); missing
  cells read as 0.  Ms is zp2's H.
* acc: the m ruler cells, one blank hole H among them.  The cell after H is the
  current column j; H moves one cell per j-step and is rewound after a B row.
* Mr holds a, the A entry of the current B row: M = 0, B = 1.
* P is the only blank of B.  It starts in front of B and slides through it: one
  cell per j-step (the cell after P moves into P).  The cell v that moved is
  multiplied by a and XORed into acc[j].  When H reaches Mr the B row is done:
  Mr := M, rewind H, fetch the next a (the front of A, consumed as M; past A's
  end: 0).  When P reaches the B/A boundary the C row is done.
* Setup: the 0 after 1^m becomes H, w moves one cell F (the cell after the
  ruler becomes Mr), and the reverse shift RB puts P in front of B.
* The first row is a dry row with a = 0 that finds the end of B: there is no
  B/A boundary yet, and after each B row D3 marks one ruler 1 as 0; when the
  ruler is all 0, m B rows are done and P is at B's end.
* Row end: D3 checks acc = 0^m (a 1 is marked and sent on into J1, which then
  meets the B/A boundary: wrong).  The Q pass loads the next m cells of out
  into the acc (missing cells read as 0; after the dry row: c_0's row), so a
  row is right iff its products XOR the acc back to 0.  Then N asks for more
  rows (A left) and RB shifts B back (after the dry row: all of w, inserting
  the B/A boundary M at P).
* P meets s-end (w ends inside B) or A is used up after a row: correct.
* Verdict o: blanks between M_g and Ms become 0, Ms becomes o, everything
  further F is erased (four blank-terminated stretches), then zp2's ER1.
"""
import zmul

B, M = 'B', 'M'
BITS = '01'
NB = '01M'
F, K = 'L', 'R'
DROP = {'TS', 'TS2', 'RW', 'HPF', 'HPD', 'SW', 'CA0', 'CA1', 'DR', 'DE', 'DU',
        'mP1', 'mP2', 'mYS', 'mXG', 'mXS', 'mZG', 'mZM', 'mZB', 'mZB2', 'mXU',
        'mZC', 'mZC2', 'mZC3', 'FR0', 'FR1', 'FE'}


def build():
    m = zmul.build()
    redo = {('GC', B), ('ER1', M),
            # zmul's output guard (mK1/mKP/mK4) is not used: Z_MM checks out itself
            ('mK1', '0'), ('mK1', '1'), ('mK4', B), ('mKP', '0'), ('mKP', '1'), ('mKP', M)}
    for k in [k for k in m.d if k[0] in DROP or k in redo]:
        del m.d[k]
    base = set(q for q, _ in m.d)

    def t(q, syms, w, mv, n):
        assert q not in base or q in ('GC', 'ER1', 'mK1'), q
        m.t(q, syms, w, mv, n)
    t('ER1', M, '.', 'R', 'mK1')                # H stays M (Ms)
    t('mK1', BITS, '.', 'R', 'mK1')
    t('GC', B, '.', F, 'X0')
    # ---------------- setup: Ms 1^m 0 w  ->  Ms 1^m H Mr P w ----------------
    t('X0', BITS, '.', F, 'X0')
    t('X0', M, '.', F, 'X1')                    # M_1
    t('X1', BITS, '.', F, 'X1')
    t('X1', M, '.', F, 'X2')                    # M_g
    t('X2', BITS, '.', F, 'X2')
    t('X2', M, '.', F, 'X3a')                   # Ms
    t('X3a', '1', '.', F, 'X3')
    t('X3a', '0B', '.', K, 'VC3')               # m = 0: C is empty
    t('X3', '1', '.', F, 'X3')
    t('X3', '0', B, F, 'SM')                    # the hole H of the accumulator
    t('X3', B, '.', K, 'VC3')                   # no 0: w is empty
    t('SM', B, '.', K, 'VC3')                   # w is empty
    for x in BITS:
        t('SM', x, M, F, 'SM' + x)              # Mr (a = 0); w moves by one
        for y in BITS:
            t('SM' + x, y, x, F, 'SM' + y)
        t('SM' + x, B, x, F, 'RB1')             # then P in front of B (shift from the end)
    # ---------------- dry row: count m B rows on the ruler ----------------
    t('D0', NB, '.', K, 'D0')
    t('D0', B, '.', K, 'D1')                    # P
    t('D1', BITS, '.', K, 'D1')
    t('D1', 'MB', '.', K, 'D3')                 # Mr
    t('D3', '0', '.', K, 'D3')
    t('D3', '1', '0', F, 'Z1')                  # mark; next B row (a = 0); at a row end: J1 fails
    t('D3', B, '.', F, 'Q2')                    # all 0: load the next out row
    # ---------------- j-step ----------------
    t('J1', B, '.', K, 'VC1')                   # P at s-end: |w| <= m^2
    t('J1', M, '.', K, 'VFa')                   # row done but acc != 0 (see D3)
    for v in BITS:
        t('J1', v, B, K, 'S' + v)               # slide P
        t('S' + v, B, v, K, 'T' + v)
        t('T' + v, BITS, '.', K, 'T' + v)
        t('T' + v, M, '.', K, 'W0')             # a = 0
        t('T' + v, B, '.', K, 'W' + v)          # a = 1
    for p in BITS:
        t('W' + p, BITS, '.', K, 'W' + p)
        t('W' + p, B, '.', F, 'U' + p)          # H
        for x in BITS:
            t('U' + p, x, B, K, 'Y' + str(int(x) ^ int(p)) + 'c')
    for c in BITS:
        t('Y' + c + 'c', B, c, F, 'Y2')
    t('Y2', B, '.', F, 'Z0')
    t('Z0', BITS, '.', F, 'Z1')
    t('Z0', 'MB', M, K, 'RS1')                  # B row done: Mr := M, rewind H
    t('Z1', BITS, '.', F, 'Z1')
    t('Z1', 'MB', '.', F, 'G2')
    t('G2', BITS, '.', F, 'G2')
    t('G2', B, '.', F, 'J1')
    # ---------------- rewind the accumulator hole ----------------
    t('RS1', B, '.', K, 'RS2')
    for x in BITS:
        t('RS2', x, B, F, 'RS3' + x)
        t('RS3' + x, B, x, K, 'RS1')
    t('RS2', M, '.', F, 'G1')                   # Ms
    t('G1', 'B01', '.', F, 'G1')
    t('G1', M, '.', F, 'GA')                    # Mr
    t('GA', BITS, '.', F, 'GA')
    t('GA', B, '.', F, 'FA')
    # ---------------- next a ----------------
    t('FA', BITS, '.', F, 'FB')
    t('FA', M, '.', K, 'D0')                    # P at B's end: row done, check acc = 0
    t('FA', B, '.', K, 'VC1')                   # w ends with B: |w| <= m^2
    t('FB', BITS, '.', F, 'FB')
    t('FB', M, '.', F, 'FC')
    t('FB', B, '.', K, 'D0')                    # no boundary yet: dry row
    t('FC', M, '.', F, 'FC')
    t('FC', B, '.', K, 'FD0')                   # past A's end: a = 0
    for x in BITS:
        t('FC', x, M, K, 'FD' + x)
        t('FD' + x, NB, '.', K, 'FD' + x)
        t('FD' + x, B, '.', K, 'FE' + x)        # P
        t('FE' + x, BITS, '.', K, 'FE' + x)
        t('FE' + x, 'MB', M if x == '0' else B, F, 'G2')   # Mr := a
    # ---------------- row done: check acc = 0, load the next out row ----------------
    t('Q2', B, '.', F, 'Q2')
    t('Q2', '0', B, K, 'Q4')
    t('Q2', M, '.', F, 'N1')                    # Mr: row loaded
    t('Q4', 'B01', '.', K, 'Q4')
    t('Q4', M, '.', K, 'Q5')                    # Ms
    t('Q5', BITS, '.', K, 'Q5')
    t('Q5', 'BM', '.', F, 'Q6')
    t('Q6', M, '.', F, 'Q80')                   # out used up: 0
    for y in BITS:
        t('Q6', y, B, F, 'Q7' + y)
        t('Q7' + y, BITS, '.', F, 'Q7' + y)
        t('Q7' + y, M, '.', F, 'Q8' + y)
        t('Q8' + y, BITS, '.', F, 'Q8' + y)
        t('Q8' + y, B, y, F, 'Q2')
    # ---------------- more rows? then shift B back ----------------
    t('N1', BITS, '.', F, 'N1')
    t('N1', B, '.', F, 'N2')                    # P
    t('N2', M, '.', F, 'N3')
    t('N2', BITS, '.', F, 'N4')
    t('N2', B, '.', K, 'VC1')                   # A used up
    t('N3', M, '.', F, 'N3')
    t('N3', BITS, '.', K, 'N5')                 # more rows: shift B back into P
    t('N5', M, '.', K, 'N5')
    t('N5', B, '.', K, 'RB2')                   # P
    t('N3', B, '.', K, 'VC1')                   # A used up
    t('N4', BITS, '.', F, 'N4')
    t('N4', M, '.', F, 'N3')
    t('N4', B, '.', K, 'RB2')                   # after the dry row: shift w, inserting the B/A boundary
    t('RB1', B, '.', K, 'RB2')
    for x in BITS:
        t('RB2', x, B, F, 'RB3' + x)
        t('RB3' + x, B, x, K, 'RB1')
    t('RB2', B, '.', F, 'RBM')
    t('RBM', B, M, K, 'RB1')
    t('RB2', M, '.', K, 'RS1')                  # Mr: P is in front of B
    # ---------------- verdict: Ms := o, erase right of Ms, blanks of out -> 0 ----------------
    t('VC1', B, '.', K, 'VC2')
    t('VC1', NB, '.', K, 'VC1')
    t('VC2', BITS, '.', K, 'VC2')
    t('VC2', 'MB', '.', K, 'VC3')
    t('VC3', 'B01', '.', K, 'VC3')
    t('VC3', M, '1', F, 'E1')
    t('VFa', B, '.', K, 'VFb')
    t('VFb', BITS, '.', K, 'VFb')
    t('VFb', M, '.', K, 'VF0')
    t('VF0', 'B01', '.', K, 'VF0')
    t('VF0', M, '0', F, 'E1')
    t('E1', BITS, B, F, 'E1')
    t('E1', B, '.', F, 'E2')                    # H
    t('E2', BITS, B, F, 'E2')
    t('E2', 'MB', B, F, 'E3')                   # Mr
    t('E3', BITS, B, F, 'E3')
    t('E3', B, '.', F, 'E4')                    # P
    t('E4', NB, B, F, 'E4')
    t('E4', B, '.', K, 'VW1')                    # s-end
    t('VW1', B, '.', K, 'VW1')
    t('VW1', BITS, '.', K, 'VW2')                 # o
    t('VW2', BITS, '.', K, 'VW2')
    t('VW2', B, '0', K, 'VW2')
    t('VW2', M, '.', F, 'VW3')                    # M_g
    t('VW3', BITS, '.', F, 'VW3')
    t('VW3', B, '.', F, 'ER1')
    return m


if __name__ == '__main__':
    print(len(build().states()), 'logical states')
