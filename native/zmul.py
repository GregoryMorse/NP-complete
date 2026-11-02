"""Native machine for linear-time multiplication (reference: ref/zmul_ref.py).

Built from the zp2 interpreter.  Changes:

* Tape between runs:  M_g J M_1 s M_2 fuel B storage.  The fuel is one block
  M 1^(|s|+1) and |J| short blocks M 1 (T = (|s|+2) 2^|J| - 1); the storage
  holds the queue of stacks, front first, each stack as  M c_1 c_2 .. ;
  |J| empty stacks are appended while the walker returns through J.
* Switch (peek  w 1 0): the cells c_{h+1} .. c_max (physically left of H and
  the head cell, which becomes a marker) are taken from the far end and inserted at the front of
  the storage, then the terminator M; when the storage front shows M the
  stack at the back is popped from its end into the blank cells left of H.
* Halt  1 0 0: H stays M; after the left side is erased, ER1 finds H, makes
  it the separator 0, blanks M_2 and copies s to the left with the copy loop
  GC.  The conversion of zfac turns  out 0 s  into unary numbers
  ..  y M x M z M  and z = x y is checked by marking (y outer, x inner).
* Every run is a decider run; the outcome 0 beeps (DP30) and starts J++.
"""
import zp2

B, M = 'B', 'M'
BITS = '01'
NB = '01M'
DROP = {'VA2', 'VA3', 'VA4', 'VN1', 'VN2', 'VU2', 'VFE', 'VF2', 'VG1', 'VG2', 'VG3', 'FB',
        'BD1', 'BD2', 'BD3', 'BD4', 'BD5', 'BD6', 'DP40', 'DP41', 'BEEP', 'DP30', 'DP31'}


def build():
    m = zp2.build()
    redo = {('CX', B), ('SINC', '0'), ('JINC', '0'), ('SOV', B), ('JOV2', B), ('EAs', B),
            ('RGQ1', BITS[0]), ('RGQ1', BITS[1]), ('GHH1', M), ('DW40', M), ('DW41', M),
            ('WB30', M), ('WB31', M), ('PKT01', '0'), ('PKT11', '0')}
    for k in [k for k in m.d if k[0] in DROP or k in redo]:
        del m.d[k]
    t = m.t
    # ---------------- outer loop ----------------
    for f in ('SINC', 'JINC'):
        t(f, '0', '1', 'R', 'NI')
    t('SOV', B, '0', 'R', 'NI')
    t('JOV2', B, M, 'R', 'NI')
    t('NI', NB, '.', 'R', 'NI')
    t('NI', B, M, 'R', 'GRB')                   # M_2, then the full fuel block
    t('CX', B, '1', 'L', 'DW1')
    for j in BITS:
        t('DW4' + j, M, j, 'R', 'mSB')          # short fuel block per walker step
        t('WB3' + j, M, j, 'R', 'mST')          # empty stack per step back
    t('mSB', NB, '.', 'R', 'mSB')
    t('mSB', B, M, 'R', 'mSB2')
    t('mSB2', B, '1', 'L', 'DW1')
    t('mST', NB, '.', 'R', 'mST')
    t('mST', B, '.', 'R', 'mST2')
    t('mST2', NB, '.', 'R', 'mST2')
    t('mST2', B, M, 'L', 'mRL1')
    t('mRL1', NB, '.', 'L', 'mRL1')
    t('mRL1', B, '.', 'L', 'mRL2')
    t('mRL2', NB, '.', 'L', 'mRL2')
    t('mRL2', B, '.', 'R', 'mRL3')
    t('mRL3', BITS, '.', 'R', 'mRL3')
    t('mRL3', M, '.', 'L', 'WB2')
    # result: DP3o is at the fuel's first M
    t('DP31', M, B, 'R', 'EAs')
    t('DP30', M, '0', 'R', 'EAs')               # mark: J++
    m.beep = 'DP30'
    t('EAs', B, '.', 'R', 'EAs2')
    t('EAs2', NB, B, 'R', 'EAs')                # the storage
    t('EAs2', B, '.', 'L', 'EBs')
    for o in BITS:
        t('DP2' + o, B, M, 'R', 'DP3' + o)      # M_2 was blanked by the check
        t('ER2' + o, B, '.', 'R', 'ER2' + o)
    # ---------------- switch ----------------
    t('RGQ1', NB, '.', 'L', 'RGQ1')
    for w in BITS:
        t('PKT' + w + '1', '0', '.', 'R', 'mGS')
    t('mGS', '01B', '.', 'R', 'mGS')
    t('mGS', M, '.', 'L', 'mGW')
    t('mGW', B, M, 'L', 'mTB')                  # the head cell becomes a marker M
    t('mTB', NB, '.', 'L', 'mTB')
    t('mTB', B, '.', 'R', 'mTK')
    for x in BITS:
        t('mTK', x, B, 'R', 'mC' + x)           # take the far end
    t('mTK', M, B, 'R', 'mCM')                  # marker: cells used up, terminator
    for x in NB:
        t('mC' + x, NB, '.', 'R', 'mC' + x)
        t('mC' + x, B, '.', 'R', 'mQ' + x)
        for y in NB:
            t('mQ' + x, y, x, 'R', 'mQ' + y)    # insert at the storage front
        t('mQ' + x, B, x, 'L', 'mRT')
    t('mRT', NB, '.', 'L', 'mRT')
    t('mRT', B, '.', 'R', 'mRX')
    t('mRX', BITS, '.', 'L', 'mRT2')
    t('mRX', M, '.', 'R', 'mPB0')
    t('mRT2', B, '.', 'L', 'mTB')
    t('mPB0', NB, '.', 'R', 'mPB0')
    t('mPB0', B, '.', 'L', 'mPB')
    for x in BITS:
        t('mPB', x, B, 'L', 'mL' + x)           # pop the back stack from its end
        t('mL' + x, NB, '.', 'L', 'mL' + x)
        t('mL' + x, B, '.', 'L', 'mLL' + x)
        t('mLL' + x, NB, '.', 'L', 'mLL' + x)
        t('mLL' + x, B, x, 'R', 'mBK')
    t('mBK', NB, '.', 'R', 'mBK')
    t('mBK', B, '.', 'R', 'mPB0')
    t('mPB', M, B, 'L', 'mE1')
    t('mE1', NB, '.', 'L', 'mE1')
    t('mE1', B, '.', 'L', 'RGQ1')
    # ---------------- halt: output check ----------------
    t('GHH1', M, '.', 'L', 'EL1')
    t('ER1', M, '0', 'R', 'mK1')
    t('mK1', BITS, '.', 'R', 'mK1')
    t('mK1', M, '.', 'R', 'mK2')
    t('mK2', BITS, '.', 'R', 'mK2')
    t('mK2', M, '.', 'R', 'mK3')
    t('mK3', BITS, '.', 'R', 'mK3')
    t('mK3', M, B, 'L', 'mK4')
    t('mK4', BITS, '.', 'L', 'mK4')
    t('mK4', M, '.', 'R', 'GC')
    t('GC', B, '.', 'L', 'TS')
    # conversion (zfac): targets  B .. n_3 M n_2 M n_1 M (blanks) M_g
    t('TS', NB, '.', 'L', 'TS')
    t('TS', B, M, 'R', 'TS2')
    t('TS2', BITS, '.', 'R', 'TS2')
    t('TS2', M, '.', 'L', 'HPF')
    t('RW', NB, '.', 'R', 'RW')
    t('RW', B, '.', 'L', 'HPF')
    t('HPF', '1', B, 'L', 'HPD')
    t('HPF', '0', B, 'L', 'SW')
    t('HPF', M, '.', 'L', 'mP1')
    t('HPD', M, '.', 'L', 'mP1')
    for x in '01M':
        q = 'SW' if x == M else 'CA' + x
        if x != M:
            t('HPD', x, B, 'L', q)
        t(q, NB, '.', 'L', q)
    t('CA1', B, '0', 'R', 'DR')
    t('CA0', B, '.', 'R', 'DR')
    t('SW', B, M, 'R', 'RW')
    t('DR', '0', '.', 'R', 'DR')
    t('DR', '1', '0', 'L', 'DE')
    t('DR', M, '.', 'L', 'DU')
    t('DE', '0', '.', 'L', 'DE')
    t('DE', B, '0', 'R', 'DR')
    t('DU', '0', '1', 'L', 'DU')
    t('DU', B, '.', 'R', 'RW')
    # z = x y:  .. y M x M z M
    t('mP1', '1', '.', 'L', 'mP1')
    t('mP1', M, '.', 'L', 'mP2')
    t('mP1', B, '.', 'R', 'mZC3')              # z is the only number
    t('mP2', '1', '.', 'L', 'mP2')
    t('mP2', M, '.', 'L', 'mYS')
    t('mP2', B, '.', 'R', 'mZC2')              # no y
    t('mYS', '0', '.', 'L', 'mYS')
    t('mYS', '1', '0', 'R', 'mXG')
    t('mYS', 'MB', '.', 'R', 'mZC')             # y used up
    t('mXG', '0', '.', 'R', 'mXG')
    t('mXG', M, '.', 'R', 'mXS')
    t('mXS', '0', '.', 'R', 'mXS')
    t('mXS', '1', '0', 'R', 'mZG')
    t('mXS', M, '.', 'L', 'mXU')                # x used up: unmark it
    t('mZG', '1', '.', 'R', 'mZG')
    t('mZG', M, '.', 'R', 'mZM')
    t('mZM', '0', '.', 'R', 'mZM')
    t('mZM', '1', '0', 'L', 'mZB')
    t('mZM', M, '.', 'R', 'FR0')                # z too small
    t('mZB', '0', '.', 'L', 'mZB')
    t('mZB', M, '.', 'L', 'mZB2')
    t('mZB2', '1', '.', 'L', 'mZB2')
    t('mZB2', '0', '.', 'R', 'mXS')
    t('mXU', '0', '1', 'L', 'mXU')
    t('mXU', M, '.', 'L', 'mYS')
    t('mZC', '0', '.', 'R', 'mZC')
    t('mZC', M, '.', 'R', 'mZC2')
    t('mZC2', '1', '.', 'R', 'mZC2')
    t('mZC2', M, '.', 'R', 'mZC3')
    t('mZC3', '0', '.', 'R', 'mZC3')
    t('mZC3', '1', '.', 'R', 'FR0')             # z too large
    t('mZC3', M, '.', 'R', 'FR1')
    for o in BITS:
        t('FR' + o, NB, '.', 'R', 'FR' + o)
        t('FR' + o, B, o, 'L', 'FE')
    t('FE', NB, B, 'L', 'FE')
    t('FE', B, '.', 'R', 'ER1')
    return m


if __name__ == '__main__':
    print(len(build().states()), 'logical states')
