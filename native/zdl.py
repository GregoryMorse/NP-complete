"""Native machine for discrete log mod primes in P (reference: ref/zdl_ref.py).

Built from zfac (native FACTOR): same new-instance glue, copy and unary
conversion, same result path.  After the conversion the left side reads

    B .. P M G M H M K M (gap) M_g        (last four numbers; older ones right of K)

1. Primality.  D := a copy of P at the left edge (`D M P M ...`).  For
   d = p-1 down to 2 (D shrinks at its left edge) test d | p by marking D and
   P cell for cell, resetting D as soon as it is full: p is used up exactly
   when D is all 1s.  When D is down to one cell, p is prime and that cell is
   y = 1:  `Y M P M G M H M K`.
2. Loop.  Compare Y with H (marking both); equal: accept.  Otherwise mark one
   cell of K (none left: reject), then Y := Y*G mod P: for every cell of G,
   for every cell of Y, mark the next cell of P (P resets when full), and
   finally rebuild Y at the left edge from the marked cells of P.
"""
import zfac

B, M = 'B', 'M'
BITS = '01'
NB = '01M'
DIV = {'RS1', 'RS2', 'RS3', 'SA', 'SK', 'SK2', 'RST', 'BACK', 'CHK', 'KC', 'ND', 'SHR'}


def build():
    m = zfac.build()
    for k in [k for k in m.d if k[0] in DIV or k in (('HPF', M), ('HPD', M))]:
        del m.d[k]
    t = m.t
    t('HPF', M, '.', 'L', 'E0')                 # conversion done
    t('HPD', M, '.', 'L', 'E0')

    def gap(q):                                 # a missing number: reject
        t(q, B, '0', 'L', 'FE')
    # ---------------- primality of p ----------------
    t('E0', NB, '.', 'L', 'E0')
    t('E0', B, M, 'R', 'CP1')                   # separator D | P
    t('CP1', '0', '.', 'R', 'CP1')              # copy P into D
    t('CP1', '1', '0', 'L', 'CP2')
    t('CP1', M, '.', 'L', 'CPU')
    t('CP2', NB, '.', 'L', 'CP2')
    t('CP2', B, '1', 'R', 'CP3')
    t('CP3', '1', '.', 'R', 'CP3')
    t('CP3', M, '.', 'R', 'CP1')
    t('CPU', '0', '1', 'L', 'CPU')
    t('CPU', M, '.', 'L', 'XS1')                # first d = p - 1
    t('XS1', BITS, '.', 'L', 'XS1')             # shrink D at the left edge
    t('XS1', B, '.', 'R', 'XS2')
    t('XS2', BITS, B, 'R', 'XS3')
    t('XS2', M, '.', 'R', 'FR0')                # p = 0
    t('XS3', BITS, '1', 'R', 'XS4')             # restore D, checking |D| >= 2
    t('XS3', M, '.', 'R', 'FR0')                # p = 1
    t('XS4', BITS, '1', 'R', 'XS5')
    t('XS4', M, '.', 'L', 'QL')                 # d = 1: p is prime; Y = 1
    t('XS5', BITS, '1', 'R', 'XS5')
    t('XS5', M, '.', 'R', 'X4')                 # mark P first, then D
    t('XL', NB, '.', 'L', 'XL')
    t('XL', B, '.', 'R', 'X1')
    t('X1', '0', '.', 'R', 'X1')
    t('X1', '1', '0', 'R', 'X2')
    t('X2', '1', '.', 'R', 'X3')
    t('X2', M, '.', 'L', 'XR')                  # D full: reset it now
    t('XR', '0', '1', 'L', 'XR')
    t('XR', B, '.', 'R', 'X3')
    t('X3', BITS, '.', 'R', 'X3')
    t('X3', M, '.', 'R', 'X4')
    t('X4', '0', '.', 'R', 'X4')
    t('X4', '1', '0', 'L', 'XL')
    t('X4', M, '.', 'L', 'XC')                  # p used up
    t('XC', '0', '1', 'L', 'XC')
    t('XC', M, '.', 'L', 'XD')
    t('XD', '1', '.', 'L', 'XD')
    t('XD', '0', '.', 'L', 'XS1')               # D not all 1s: d does not divide p
    t('XD', B, '.', 'R', 'FR0')                 # d divides p
    # ---------------- compare Y with H ----------------
    t('QL', NB, '.', 'L', 'QL')
    t('QL', B, '.', 'R', 'Q1')
    t('Q1', '0', '.', 'R', 'Q1')
    t('Q1', '1', '0', 'R', 'Q2')
    t('Q1', M, '.', 'R', 'QY1')                 # Y used up
    t('Q2', BITS, '.', 'R', 'Q2')
    t('Q2', M, '.', 'R', 'Q3')
    for a, b in (('Q3', 'Q4'), ('Q4', 'Q5'), ('QY1', 'QY2'), ('QY2', 'QY3'), ('QK', 'KD')):
        t(a, BITS, '.', 'R', a)
        t(a, M, '.', 'R', b)
    for q in ('Q4', 'Q5', 'QY2', 'QY3', 'KD'):
        gap(q)
    t('Q5', '0', '.', 'R', 'Q5')
    t('Q5', '1', '0', 'L', 'QL')
    t('Q5', M, '.', 'R', 'KD')                  # H used up first: not equal
    t('QY3', '0', '.', 'R', 'QY3')
    t('QY3', '1', '.', 'R', 'QK')               # H longer: not equal
    t('QY3', M, '.', 'R', 'FR1')                # equal: accept
    t('KD', '0', '.', 'R', 'KD')                # e += 1
    t('KD', '1', '0', 'L', 'KB')
    t('KD', M, '.', 'R', 'FR0')                 # e > k: reject
    t('KB', '0', '.', 'L', 'KB')
    t('KB', M, '.', 'L', 'QU1')
    t('QU1', '0', '1', 'L', 'QU1')              # unmark H, then Y
    t('QU1', '1', '.', 'L', 'QU1')
    t('QU1', M, '.', 'L', 'QU2')
    for a, b in (('QU2', 'QU3'), ('QU3', 'QU4')):
        t(a, BITS, '.', 'L', a)
        t(a, M, '.', 'L', b)
    t('QU4', '0', '1', 'L', 'QU4')
    t('QU4', '1', '.', 'L', 'QU4')
    t('QU4', B, '.', 'R', 'O1')                 # outer loop picks a cell of G first
    # ---------------- Y := Y * G mod P ----------------
    t('I1', '0', '.', 'R', 'I1')
    t('I1', '1', '0', 'R', 'I2')
    t('I1', M, '.', 'L', 'IU')                  # Y used up
    t('I2', '1', '.', 'R', 'I2')
    t('I2', M, '.', 'R', 'I3')
    t('I3', '0', '.', 'R', 'I3')
    t('I3', '1', '0', 'R', 'I3B')               # Z += 1 ...
    t('I3B', '1', '.', 'L', 'LE')
    t('I3B', M, '.', 'L', 'W')                  # ... mod p
    t('W', '0', '1', 'L', 'W')
    t('W', M, '.', 'L', 'LE')
    t('LE', NB, '.', 'L', 'LE')
    t('LE', B, '.', 'R', 'I1')
    t('IU', '0', '1', 'L', 'IU')
    t('IU', B, '.', 'R', 'O1')
    t('O1', '1', '.', 'R', 'O1')
    t('O1', M, '.', 'R', 'O2')
    t('O2', BITS, '.', 'R', 'O2')
    t('O2', M, '.', 'R', 'O3')
    t('O3', '0', '.', 'R', 'O3')
    t('O3', '1', '0', 'L', 'LE')                # next cell of G
    t('O3', M, '.', 'L', 'RB1')                 # G used up
    t('RB1', '0', '1', 'L', 'RB1')
    t('RB1', M, '.', 'L', 'RB2')
    t('RB2', BITS, '.', 'L', 'RB2')
    t('RB2', M, '.', 'L', 'RB3')
    t('RB3', '1', B, 'L', 'RB3')                # erase the old Y
    t('RB3', B, '.', 'R', 'T0')
    t('T0', B, '.', 'R', 'T0')
    t('T0', M, '.', 'R', 'T1')
    t('T1', '1', '.', 'R', 'T1')                # each marked cell of P adds 1 to Y
    t('T1', '0', '1', 'L', 'T2')
    t('T1', M, '.', 'L', 'QL')
    t('T2', NB, '.', 'L', 'T2')
    t('T2', B, '1', 'R', 'T3')
    t('T3', '1', '.', 'R', 'T3')
    t('T3', M, '.', 'R', 'T1')
    return m


if __name__ == '__main__':
    print(len(build().states()), 'logical states')
