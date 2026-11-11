"""Native machine for NP in P/poly (reference: ref/zppoly_ref.py).

Built from zp2.  Tape between runs:

    M_g K M_1 a M_a s M_2 C M_3 M B_1          (verifier phase)
    M_g K M_1 a M_a s M_2 M [1] M_3 M B_R .. M B_1   (decider phase)

K is the degree (it plays J's part: the walker builds |K|+1 fuel blocks), a
the advice program (the decider's code is the field before its source s),
s the instance, a binary counter of fixed length n.

Before a decider run, a is charged: for each cell of a (blanked while the
fuel is decremented, its bit kept in the state) the fuel is decremented once.
Exhausting the fuel there means |a| > T(K, n): the machine beeps (BEEPX),
erases everything right of M_1 and moves to K + 1, n = 0, a = ''.

After a decider run: correct -> s + 1 (binary); an overflow appends a cell
to s (n + 1) and deletes a cell by cell.  Wrong -> s := 0^n, a := a + 1
(shortlex; a carry out of a lengthens it, shifting M_a and s by one cell).
"""
import zp2

B, M = 'B', 'M'
BITS = '01'
NB = '01M'


def build():
    m = zp2.build()
    t = m.t

    def drop(q, syms):
        for a in syms:
            del m.d[(q, a)]

    def redo(q, syms, w, mv, n):
        drop(q, syms)
        t(q, syms, w, mv, n)
    # start: M_g, M_1, M_a, then GRB writes M_2
    redo('JOV2', B, M, 'R', 'JX2')
    t('JX2', B, M, 'R', 'GRB')
    # extra field a: BLK copies s, dispatchers skip a
    redo('BN3', M, '.', 'R', 'BNA')
    t('BNA', BITS, '.', 'R', 'BNA')
    t('BNA', M, '.', 'R', 'COPY')
    redo('BD3', M, '.', 'R', 'BDA')
    t('BDA', BITS, '.', 'R', 'BDA')
    t('BDA', M, '.', 'R', 'BD4')
    redo('DG3', M, '.', 'R', 'DGA')             # decider: skip K, a; copy s
    t('DGA', BITS, '.', 'R', 'DGA')
    t('DGA', M, '.', 'R', 'GC')
    redo('VG3', M, '.', 'R', 'VGA')             # verifier: skip K, a, s; copy C
    t('VGA', BITS, '.', 'R', 'VGA')
    t('VGA', M, '.', 'R', 'DGA')
    for o in BITS:
        redo('DP1' + o, M, '.', 'R', 'DPX' + o)
        t('DPX' + o, BITS, '.', 'R', 'DPX' + o)
        t('DPX' + o, M, '.', 'R', 'DP2' + o)
    # charge |a| fuel units before the decider run (H is written afterwards)
    redo('WB2', B, '.', 'R', 'CHS')
    t('CHS', M, '.', 'R', 'CK')
    t('CK', BITS, '.', 'R', 'CK')
    t('CK', M, '.', 'R', 'CA')
    t('CA', M, '.', 'L', 'CDN')                 # all of a charged
    t('CDN', NB, '.', 'L', 'CDN')
    t('CDN', B, M, 'R', 'DG2')                  # H
    for b in BITS:
        t('CA', b, B, 'R', 'XR' + b)
        t('XR' + b, NB, '.', 'R', 'XR' + b)
        t('XR' + b, B, '.', 'L', 'XD1' + b)
        t('XD1' + b, '0', '.', 'L', 'XD' + b)
        t('XD1' + b, '1', '0', 'L', 'XK' + b)
        t('XD1' + b, M, '.', 'R', 'BEEPX')      # |a| > T(K, n)
        t('XD' + b, '0', '.', 'L', 'XD' + b)
        t('XD' + b, '1', '0', 'L', 'XK' + b)
        t('XD' + b, M, '.', 'R', 'XF' + b)
        t('XF' + b, '0', '1', 'R', 'XF' + b)
        t('XF' + b, 'MB', '.', 'L', 'XG' + b)
        t('XG' + b, '1', '.', 'L', 'XG' + b)
        t('XG' + b, M, '.', 'L', 'XD1' + b)
        t('XK' + b, NB, '.', 'L', 'XK' + b)
        t('XK' + b, B, b, 'R', 'CA')
    # beep: erase everything right of M_1, then K + 1
    t('BEEPX', M, '.', 'R', 'EXC')
    m.beep = 'BEEPX'
    t('EXC', NB, '.', 'R', 'EXC')
    t('EXC', B, '.', 'L', 'EXD')
    t('EXD', NB, B, 'L', 'EXD')
    t('EXD', B, '.', 'L', 'EXG')                # the blanked cell of a
    t('EXG', BITS, B, 'L', 'EXG')
    t('EXG', M, '.', 'L', 'JINC')
    redo('JINC', '0', '1', 'R', 'JX1')
    t('JX1', BITS, '.', 'R', 'JX1')
    t('JX1', M, '.', 'R', 'JX2')
    for q in ('JE3',):
        for a in BITS + M:
            m.d.pop((q, a), None)
    # wrong answer: s := 0^n, a + 1
    drop('BEEP', M)
    redo('DP41', M, '.', 'L', 'WRG')
    redo('DP40', '1', '.', 'L', 'WRG')
    t('WRG', M, '0', 'R', 'EAs')
    redo('EBj', M, B, 'L', 'ZS')
    t('ZS', '1', '0', 'L', 'ZS')
    t('ZS', '0', '.', 'L', 'ZS')
    t('ZS', M, '.', 'L', 'AINC')
    t('AINC', '1', '0', 'L', 'AINC')
    t('AINC', '0', '1', 'R', 'GRB')
    t('AINC', M, '.', 'R', 'AOV')
    t('AOV', '0', '.', 'R', 'AOV')
    t('AOV', M, '0', 'R', 'AOV2')
    t('AOV2', '0', M, 'R', 'AOV3')
    t('AOV2', B, M, 'R', 'GRB')
    t('AOV3', '0', '.', 'R', 'AOV3')
    t('AOV3', B, '0', 'R', 'GRB')
    # correct: s + 1; overflow: n + 1 and a := ''
    redo('SOV', B, '0', 'L', 'DL5')
    t('DL5', '0', '.', 'L', 'DL5')
    t('DL5', M, '.', 'L', 'DL1')
    t('DL1', BITS, M, 'R', 'DL2')
    t('DL1', M, '.', 'R', 'GRB')
    t('DL2', M, '0', 'R', 'DL3')
    t('DL3', '0', '.', 'R', 'DL3')
    t('DL3', B, '.', 'L', 'DL4')
    t('DL4', '0', B, 'L', 'DL5')
    return m
