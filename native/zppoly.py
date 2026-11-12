"""Native machine for NP in P/poly (reference: ref/zppoly_ref.py).

Built from zp2.  Tape between runs:

    M_g K M_1 a M_a s M_2 C M_3 M B_1                (verifier phase)
    M_g K M_1 a M_a s M_2 M [1] M_3 M B_R .. M B_1   (decider phase)

K is the degree, stored last bit first (it plays J's part: the walker builds
|K|+1 fuel blocks), a the advice program (the decider's code is the field
before its source s), s the instance, a binary counter of fixed length n.

BLK dispatch.  zp2 counts fields from the left after each BLK; here the copy
loop's exit CX looks at the cell after M_2 instead: a 1 is C (being built, or
built: verifier fuel), an M the decider's truth flag (decider fuel block).

Charge.  When the walker is home it writes H and blanks M_a; the guest copy
loop GC then copies a as tokens to the left (a blank, not M, ends it, and GC,B
writes M_a back), giving

    M_t t_2 .. t_k H M_g K M_1 a M_a ...      (M_t replaces the first token)

H becomes the gap of the zp2 fuel loop, which is entered at FR: each
decrement returns through FBACK to PK1, which skips the tokens to M_t
(PK1,M is new); M_t then moves one token right (U) and the next decrement
starts (V).  With no token left U writes H back.  So the fuel is decremented
|a| times.  Exhausting it there (|a| > T(K, n)) ends in zp2's EXH: GHH0 turns
M_g into 0, EL2 erases the tokens and meets M_t (EL2,M is new); Z3 restores
M_g and the machine beeps (BEEPX).  BEEPX is the first state of K + 1, which
runs from the left since K is reversed (KINC carries, J2 skips to M_1; a carry
out writes 0 over M_1 and JOV2 writes M_1 one cell right).  Then the verifier's
eraser VA3/VA4 erases everything right of M_1, FB writes M_a and GRB M_2:
K + 1, n = 0, a = ''.  At the start I0 writes M_g and JOV2 does the same for K = ''.

Decider run: zp2's comparison; zp2's BEEP state is no longer the beep, it
only marks a wrong answer (EBs then goes to EBj).
Wrong answer: s := 0^n (ZS), a := a + 1 with zp2's SINC; its overflow state
SOV meets M_a (not a blank) and lengthens a: it writes 0 over M_a, FB writes
M_a over the first cell of s and AOV3 appends a 0 to s.
Correct answer: s + 1 (SINC); an overflow (SOV meets a blank) appends a cell
to s (n + 1) and deletes a cell by cell (DL5, DL1, DL3, DL4).
"""
import zp2

B, M = 'B', 'M'
BITS = '01'
NB = '01M'


def build():
    m = zp2.build()
    t = m.t
    for k in [k for k in m.d if k[0] in ('BD1', 'BD2', 'BD3', 'BD4', 'BD5', 'BD6', 'JE3', 'JINC', 'JOV')]:
        del m.d[k]

    def redo(q, syms, w, mv, n):
        for a in syms:
            m.d.pop((q, a), None)
        t(q, syms, w, mv, n)
    # start, and K + 1 after a beep: M_1, erase the rest, M_a (FB), M_2 (GRB)
    redo('JOV2', NB + B, M, 'R', 'VA3')
    # extra field a: BLK copies s, the run setups skip a
    redo('BN3', M, '.', 'R', 'BNA')
    t('BNA', BITS, '.', 'R', 'BNA')
    t('BNA', M, '.', 'R', 'COPY')
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
    # BLK dispatch at the cell after M_2
    redo('CX', '1', '.', 'R', 'CXC')
    redo('CX', M, '.', 'R', 'CXD')
    redo('CX', B, '1', 'R', 'FB')               # C built (n = 0): M_3, verifier fuel
    t('CXC', '1', '.', 'R', 'CXC')
    t('CXC', B, '1', 'R', 'FB')                 # C built: M_3, verifier fuel
    t('CXC', M, '.', 'R', 'CXV')
    t('CXV', 'M1', '.', 'R', 'CXV')
    t('CXV', B, '1', 'L', 'VG1')                # verifier fuel built
    t('CXD', 'M1', '.', 'R', 'CXD')
    t('CXD', B, '1', 'L', 'DW1')                # decider fuel block built
    # charge: walker home -> H, blank M_a, copy a as tokens (GC)
    redo('WB2', B, M, 'R', 'CHS')
    t('CHS', M, '.', 'R', 'CK')
    t('CK', BITS, '.', 'R', 'CK')
    t('CK', M, '.', 'R', 'CK2')
    t('CK2', BITS, '.', 'R', 'CK2')
    t('CK2', M, B, 'L', 'CK3')
    t('CK3', BITS, '.', 'L', 'CK3')
    t('CK3', M, '.', 'R', 'GC')
    t('GC', B, M, 'L', 'CD')                    # end of a: M_a back
    t('CD', NB, '.', 'L', 'CD')
    t('CD', B, '.', 'R', 'U')
    t('U', BITS, M, 'R', 'V')                   # M_t takes a token
    t('U', B, M, 'R', 'DG2')                    # no token left: H
    t('U', M, '.', 'R', 'DG2')                  # a = '': H stays
    t('V', BITS, '.', 'R', 'V')
    t('V', M, B, 'R', 'FR')                     # H becomes the gap
    t('V', B, '.', 'R', 'FR')
    t('PK1', M, B, 'R', 'U')                    # decremented: next token
    # exhausted (|a| > T): M_g is 0, tokens erased up to M_t
    t('EL2', M, B, 'R', 'Z3')
    t('Z3', B, '.', 'R', 'Z3')
    t('Z3', '0', M, 'R', 'BEEPX')
    m.beep = 'BEEPX'
    for q in ('BEEPX', 'KINC'):                 # K + 1; K is stored last bit first
        t(q, '1', '0', 'R', 'KINC')
        t(q, '0', '1', 'R', 'J2')
        t(q, M, '0', 'R', 'JOV2')               # carry out: M_1 moves right
    t('J2', BITS, '.', 'R', 'J2')
    t('J2', M, '.', 'R', 'VA3')
    # decider run: zp2's comparison; its BEEP state only marks a wrong answer
    # wrong: s := 0^n, a := a + 1 (SINC); a carry lengthens a
    redo('EBj', M, B, 'L', 'ZS')
    t('ZS', '1', '0', 'L', 'ZS')
    t('ZS', '0', '.', 'L', 'ZS')
    t('ZS', M, '.', 'L', 'SINC')
    t('SOV', M, '0', 'R', 'FB')                 # M_a moves right: FB as for M_3
    t('FB', '0', M, 'R', 'AOV3')
    t('AOV3', '0', '.', 'R', 'AOV3')
    t('AOV3', B, '0', 'R', 'GRB')
    # correct: s + 1; overflow: n + 1 and a := ''
    redo('SOV', B, '0', 'L', 'DL5')
    t('DL5', '0', '.', 'L', 'DL5')
    t('DL5', M, '.', 'L', 'DL1')
    t('DL1', BITS, M, 'R', 'DL3')
    t('DL1', M, '.', 'R', 'GRB')
    t('DL3', M, '0', 'R', 'DL3')
    t('DL3', '0', '.', 'R', 'DL3')
    t('DL3', B, '.', 'L', 'DL4')
    t('DL4', '0', B, 'L', 'DL5')
    return m
