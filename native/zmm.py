"""Native machine for the GF(2) matrix product in linear time (reference: ref/zmm_ref.py).

Z_MUL (native/zmul.py) with a new output check.  The guest model, the switch,
the fuel, the copy of s next to out and the dispatch are zmul's; H stays M.

Check layout (logical direction = physical left, away from M_g):

    M_g out Ms 1^m Mr [B rows, P] [A] s-end a [acc_old] sep [acc_new] end

* out = c_0 c_1 ..; consumed cells become blank (from the M_g side); missing
  cells read as 0.  Ms is H.  The 0 after the ruler 1^m becomes Mr.
* P is the only blank of w.  It starts in front of B (w is shifted by one) and
  slides through B: one cell per j-step (the cell after P moves into P).  After
  a row P sits after B; the reverse shift puts it back.
* A is consumed from its front; consumed cells are M.  a is the A cell of the
  current B row, kept in the a-cell: the first bit after the M-run that follows
  s-end.  Consumed acc_old cells are M.
* A j-step reads v after P, goes to the acc, consumes the front o of acc_old
  and appends o xor (a v) to acc_new; then P slides.  When acc_old is used up
  the B row is done: mark the ruler, fetch the next a (A's front, or 0 past A's
  end, or 0 in the dry row), and acc_new becomes acc_old.
* When the ruler is used up the row is done.  The first row is a dry run with
  a = 0 that only finds the end of B: its last j-step finds A's first cell
  after P, which becomes the first a.  Every other row compares acc_new with
  the next m cells of out, fetches the next row's first a (A used up: correct),
  zeroes the acc and shifts B back.
* If P reaches s-end in the dry row, A is empty: correct.
* Verdict o: blanks between M_g and Ms become 0, Ms becomes o, everything
  further left is erased (four blank-terminated stretches), then zp2's ER1.
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
    redo = {('GC', B), ('ER1', M)}
    for k in [k for k in m.d if k[0] in DROP or k in redo]:
        del m.d[k]
    t = m.t
    t('ER1', M, '.', 'R', 'mK1')                # H stays M (Ms)
    t('GC', B, '.', F, 'X0')
    # ---------------- setup ----------------
    t('X0', BITS, '.', F, 'X0')
    t('X0', M, '.', F, 'X1')                    # M_1
    t('X1', BITS, '.', F, 'X1')
    t('X1', M, '.', F, 'X2')                    # M_g
    t('X2', BITS, '.', F, 'X2')
    t('X2', M, '.', F, 'X3')                    # Ms
    t('X3', '1', '.', F, 'X3')
    t('X3', '0B', M, F, 'SH')                   # Mr
    t('SH', B, '.', F, 'AI')
    for x in BITS:
        t('SH', x, B, F, 'SH' + x)              # P in front of w
        for y in BITS:
            t('SH' + x, y, x, F, 'SH' + y)
        t('SH' + x, B, x, F, 'AI')
    t('AI', B, '.', F, 'AI2')
    t('AI2', B, '0', K, 'AB0')                  # a = 0
    t('AB0', BITS, '.', K, 'AB0')
    t('AB0', B, '.', K, 'AB1')
    t('AB1', BITS, '.', K, 'AB1')
    t('AB1', B, '.', K, 'AB2')
    t('AB2', BITS, '.', K, 'AB2')
    t('AB2', M, '.', K, 'AB3')
    t('AB3', '0', '.', K, 'AB3')
    t('AB3', '1', '0', F, 'AF1')                # acc_old := 0^m
    t('AB3', M, '.', F, 'RR')
    t('AF1', '0', '.', F, 'AF1')
    t('AF1', M, '.', F, 'AF2')
    t('AF2', BITS, '.', F, 'AF2')
    t('AF2', B, '.', F, 'AF3')
    t('AF3', BITS, '.', F, 'AF3')
    t('AF3', B, '.', F, 'AF4')
    t('AF4', BITS, '.', F, 'AF4')
    t('AF4', B, '0', K, 'AB0')
    t('RR', '0', '1', F, 'RR')
    t('RR', M, '.', F, 'RR2')
    t('RR2', BITS, '.', F, 'RR2')
    t('RR2', B, '.', F, 'J1')
    # ---------------- j-step ----------------
    t('J0', B, '.', F, 'J1')
    t('J1', B, '.', K, 'VB')                    # P at s-end in the dry row: A empty
    t('J1', '1', '.', F, 'JF1')
    t('J1', '0M', '.', F, 'JF0')
    for v in BITS:
        t('JF' + v, NB, '.', F, 'JF' + v)
        t('JF' + v, B, '.', F, 'JA' + v)
        t('JA' + v, M, '.', F, 'JA' + v)
        for a in BITS:
            t('JA' + v, a, '.', F, 'JC' + str(int(a) & int(v)))
    for p in BITS:
        t('JC' + p, M, '.', F, 'JC' + p)
        for o in BITS:
            t('JC' + p, o, M, F, 'JW' + str(int(o) ^ int(p)))
        t('JC' + p, B, '.', K, 'TR1')           # acc_old used up: B row done
    for c in BITS:
        t('JW' + c, BITS, '.', F, 'JW' + c)
        t('JW' + c, B, '.', F, 'JX' + c)
        t('JX' + c, BITS, '.', F, 'JX' + c)
        t('JX' + c, B, c, K, 'JB')
    t('JB', NB, '.', K, 'JB')
    t('JB', B, '.', K, 'JB2')
    t('JB2', NB, '.', K, 'JB2')
    t('JB2', B, '.', K, 'JB3')
    t('JB3', NB, '.', K, 'JB3')
    t('JB3', B, '.', F, 'SL1')
    for x in BITS:
        t('SL1', x, B, K, 'SL2' + x)            # slide P
        t('SL2' + x, B, x, F, 'J0')
    # ---------------- next B row ----------------
    t('TR1', NB, '.', K, 'TR1')
    t('TR1', B, '.', K, 'TR2')
    t('TR2', NB, '.', K, 'TR2')
    t('TR2', B, '.', K, 'TR3')
    t('TR3', BITS, '.', K, 'TR3')
    t('TR3', M, '.', K, 'TR4')
    t('TR4', '0', '.', K, 'TR4')
    t('TR4', '1', '0', K, 'TR5')
    t('TR4', M, '.', F, 'RE1')                  # m = 0
    t('TR5', '1', '.', F, 'FA1')
    t('TR5', M, '.', F, 'RE1')                  # last B row done: row done
    t('FA1', '0', '.', F, 'FA1')
    t('FA1', M, '.', F, 'FA2')
    t('FA2', BITS, '.', F, 'FA2')
    t('FA2', B, '.', F, 'FA3')
    t('FA3', NB, '.', F, 'FA3')
    t('FA3', B, '.', K, 'FA4')
    t('FA4', BITS, '.', K, 'FA4')
    t('FA4', M, '.', F, 'FA5')
    t('FA4', B, '.', F, 'FC0')                  # dry row: a = 0
    t('FA5', '0', M, F, 'FC0')
    t('FA5', '1', M, F, 'FC1')
    t('FA5', B, '.', F, 'FE0')                  # past A's end: a = 0
    for a in BITS:
        t('FC' + a, NB, '.', F, 'FC' + a)
        t('FC' + a, B, '.', F, 'FE' + a)
        t('FE' + a, M, '.', F, 'FE' + a)
        t('FE' + a, BITS, M, F, 'FG' + a)
        t('FG' + a, M, '.', F, 'FG' + a)
        t('FG' + a, B, a, K, 'FR1')
    t('FR1', NB, '.', K, 'FR1')
    t('FR1', B, '.', K, 'FR2')
    t('FR2', NB, '.', K, 'FR2')
    t('FR2', B, '.', F, 'J1')
    # ---------------- row done ----------------
    t('RE1', '0', '1', F, 'RE1')
    t('RE1', M, '.', F, 'RE2')
    t('RE2', BITS, '.', F, 'RE2')
    t('RE2', B, '.', F, 'RE3')
    t('RE3', '0', M, F, 'DC0')                  # dry row: A's first cell is a
    t('RE3', '1', M, F, 'DC1')
    t('RE3', M, '.', F, 'CF4')                  # compare acc_new with out
    for a in BITS:
        t('DC' + a, NB, '.', F, 'DC' + a)
        t('DC' + a, B, '.', F, 'SE' + a)
        t('SE' + a, M, '.', F, 'SE' + a)
        t('SE' + a, BITS, M, F, 'SG' + a)
        t('SG' + a, M, '.', F, 'SG' + a)
        t('SG' + a, B, a, F, 'ZR')
    t('ZR', NB, '0', F, 'ZR')
    t('ZR', B, '.', K, 'ZB')
    t('ZB', NB, '.', K, 'ZB')
    t('ZB', B, '.', K, 'ZB2')
    t('ZB2', NB, '.', K, 'ZB2')
    t('ZB2', B, '.', K, 'RS1')
    for x in BITS:
        t('RS1', x, B, F, 'RSW' + x)            # shift B back
        t('RSW' + x, B, x, K, 'RS0')
    t('RS0', B, '.', K, 'RS1')
    t('RS1', M, '.', F, 'J0')
    t('CM', M, '.', F, 'CM')
    t('CM', B, '.', K, 'NF')
    for x in BITS:
        t('CM', x, M, K, 'CB' + x)
        t('CB' + x, NB, '.', K, 'CB' + x)
        t('CB' + x, B, '.', K, 'CB2' + x)
        t('CB2' + x, NB, '.', K, 'CB2' + x)
        t('CB2' + x, B, '.', K, 'CB3' + x)
        t('CB3' + x, NB, '.', K, 'CB3' + x)
        t('CB3' + x, B, '.', K, 'CB4' + x)
        t('CB4' + x, BITS, '.', K, 'CB4' + x)
        t('CB4' + x, M, '.', K, 'CB5' + x)
        t('CB5' + x, BITS, '.', K, 'CB5' + x)
        t('CB5' + x, M, '.', K, 'CB6' + x)
        t('CB6' + x, BITS, '.', K, 'CB6' + x)
        t('CB6' + x, 'BM', '.', F, 'CB7' + x)
        t('CB7' + x, x, B, F, 'CF1')
        t('CB7' + x, str(1 - int(x)), '.', K, 'VF0')    # mismatch
    t('CB70', M, '.', F, 'CF2')                 # out used up: 0
    t('CB71', M, '.', K, 'VF0')
    t('CF1', BITS, '.', F, 'CF1')
    t('CF1', M, '.', F, 'CF2')
    t('CF2', BITS, '.', F, 'CF2')
    t('CF2', M, '.', F, 'CF3')
    t('CF3', BITS, '.', F, 'CF3')
    t('CF3', B, '.', F, 'CF4')
    t('CF4', NB, '.', F, 'CF4')
    t('CF4', B, '.', F, 'CF5')
    t('CF5', NB, '.', F, 'CF5')
    t('CF5', B, '.', F, 'CM')
    t('NF', NB, '.', K, 'NF')
    t('NF', B, '.', K, 'NF2')
    t('NF2', NB, '.', K, 'NF2')
    t('NF2', B, '.', K, 'NF3')
    t('NF3', BITS, '.', K, 'NF3')
    t('NF3', M, '.', F, 'NF4')
    t('NF4', '0', M, F, 'DC0')
    t('NF4', '1', M, F, 'DC1')
    t('NF4', B, '.', K, 'VB')                   # A used up: correct
    # ---------------- verdict ----------------
    t('VB', NB, '.', K, 'VB')
    t('VB', B, '.', K, 'VC')
    t('VC', BITS, '.', K, 'VC')
    t('VC', M, '.', K, 'VD')
    t('VD', BITS, '.', K, 'VD')
    t('VD', M, '.', K, 'VF1')
    for o in BITS:
        q = 'VF' + o
        t(q, '01B', '.', K, q)
        t(q, M, '.', F, 'FB' + o)
        t('FB' + o, B, '0', F, 'FB' + o)
        t('FB' + o, BITS, '.', F, 'FB' + o)
        t('FB' + o, M, o, F, 'E1')
    for i in range(1, 5):
        t('E%d' % i, NB, B, F, 'E%d' % i)
        t('E%d' % i, B, '.', F if i < 4 else K, 'E%d' % (i + 1) if i < 4 else 'ER1')
    return m


if __name__ == '__main__':
    print(len(build().states()), 'logical states')
