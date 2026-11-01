"""Z_P v2 as a 4-symbol logical machine (see docs/native.md for the layout).

Tape between runs:  B* M_g J M_1 s M_2 C M_3 M B_R ... M B_1 B*
During a run the left side holds  Q (rotated code) , a blank gap (and jump
tokens M), and the guest tape reversed:  c_max .. c_h H c_{h-1} .. c_0 M_g.
"""
from logic import LTM

B, M = 'B', 'M'
BITS = '01'
NB = '01M'          # non-blank
ALL = 'BM01'


def build():
    m = LTM('I0')
    t = m.t
    # ---------------- interpreter ----------------
    t('NAV', '01B', '.', 'R', 'NAV')
    t('NAV', M, '.', 'R', 'MRUN')
    t('MRUN', M, '.', 'R', 'MRUN')
    t('MRUN', B, '.', 'L', 'CONS')
    t('MRUN', BITS, '.', 'L', 'BK2')
    t('CONS', M, B, 'L', 'CN2')
    t('CN2', M, '.', 'L', 'TW')
    t('CN2', B, '.', 'R', 'NAV')
    t('BK2', M, '.', 'L', 'BK2')
    t('BK2', '1', '0', 'L', 'GQ1')          # iota countdown on c_h
    t('BK2', '0', B, 'L', 'GQ1')
    t('BK2', B, '.', 'R', 'FR')             # countdown done: fuel
    t('GQ1', BITS, '.', 'L', 'GQ1')
    t('GQ1', B, '.', 'L', 'TW')
    # fuel: odometer of thermometer blocks at the far right
    t('FR', NB, '.', 'R', 'FR')
    t('FR', B, '.', 'L', 'DEC1')
    t('DEC1', '0', '.', 'L', 'DEC')
    t('DEC1', '1', '0', 'L', 'FBACK')
    t('DEC1', M, '.', 'L', 'EXH')
    t('DEC', '0', '.', 'L', 'DEC')
    t('DEC', '1', '0', 'L', 'FBACK')
    t('DEC', M, '.', 'R', 'RF')
    t('RF', '0', '1', 'R', 'RF')
    t('RF', 'MB', '.', 'L', 'RG')
    t('RG', '1', '.', 'L', 'RG')
    t('RG', M, '.', 'L', 'DEC1')
    t('FBACK', NB, '.', 'L', 'FBACK')
    t('FBACK', B, '.', 'L', 'PK1')
    # peek w d t at Q's right end
    t('PK1', BITS, '.', 'L', 'PK1')
    t('PK1', B, '.', 'L', 'PK2')
    t('PK2', B, '.', 'L', 'PK2')
    for w in BITS:
        t('PK2', w, '.', 'L', 'PKD' + w)
        t('PKD' + w, B, '.', 'R', 'GHH' + w)
        for d in BITS:
            t('PKD' + w, d, '.', 'L', 'PKT' + w + d)
            t('PKT' + w + d, '1', '.', 'R', 'GH' + w + d)
            t('PKT' + w + d, '0B', '.', 'R', 'GHH' + w)
            t('GH' + w + d, '01B', '.', 'R', 'GH' + w + d)
        t('GH' + w + '1', M, w, 'L', 'PUTH')
        t('GH' + w + '0', M, '.', 'L', 'WC' + w)
        t('WC' + w, ALL, w, 'R', 'A')
    t('PUTH', ALL, M, 'L', 'RGQ1')
    t('A', M, '.', 'R', 'BB')
    t('BB', M, '.', 'L', 'BB2')
    t('BB2', M, '.', 'L', 'RGQ1')
    for y in BITS:
        t('BB', y, M, 'L', 'Y' + y)
        t('Y' + y, M, y, 'L', 'RGQ1')
    t('RGQ1', BITS, '.', 'L', 'RGQ1')
    t('RGQ1', B, '.', 'L', 'RTW')
    # rotations: move one entry  w d 1^k 0  from Q's right end to its left end.
    # A recording rotation (entered at RTW) leaves a token M in place of w, d
    # and each 1; the return sweep sees the vacated cell and keeps the mode.
    for first, wr in (('TW', B), ('RTW', M)):
        t(first, 'BM', '.', 'L', first)
        for b in BITS:
            t(first, b, wr, 'L', 'C' + b + 'D')
    for X in 'DO':
        for b in BITS:
            c = 'C' + b + X
            t(c, BITS, '.', 'L', c)
            t(c, B, b, 'R', 'RET' + X)
        t('RET' + X, BITS, '.', 'R', 'RET' + X)
        t('RET' + X, B, '.', 'L', 'T' + X)
        t('RET' + X, M, '.', 'L', 'RT' + X)
    for pre, wr in (('', B), ('R', M)):
        for b in BITS:
            t(pre + 'TD', b, wr, 'L', 'C' + b + 'O')
        t(pre + 'TO', '1', wr, 'L', 'C1O')
        t(pre + 'TO', '0', B, 'L', 'C0E')
    t('C0E', BITS, '.', 'L', 'C0E')
    t('C0E', B, '0', 'R', 'NAV')
    # halt: outcome w goes into c_h, then the left side is erased
    t('EXH', NB, '.', 'L', 'EXH')
    t('EXH', B, '0', 'L', 'EL2')
    for w in BITS:
        t('GHH' + w, '01B', '.', 'R', 'GHH' + w)
        t('GHH' + w, M, '.', 'L', 'WRO' + w)
        t('WRO' + w, ALL, w, 'L', 'EL2')
    t('EL2', BITS, B, 'L', 'EL2')
    t('EL2', B, '.', 'L', 'EL3')
    t('EL3', B, '.', 'L', 'EL3')
    t('EL3', BITS, B, 'L', 'EL4')
    t('EL4', BITS, B, 'L', 'EL4')
    t('EL4', B, '.', 'R', 'ER1')
    t('ER1', B, '.', 'R', 'ER1')
    for o in BITS:
        t('ER1', o, B, 'R', 'ERH' + o)
        t('ERH' + o, M, B, 'R', 'ER2' + o)
        t('ER2' + o, BITS, B, 'R', 'ER2' + o)
        t('ER2' + o, M, '.', 'R', 'DP1' + o)
    outer(m)
    return m


def outer(m):
    t = m.t
    # ---------------- result dispatch (head right of M_g) ----------------
    for o in BITS:
        t('DP1' + o, BITS, '.', 'R', 'DP1' + o)
        t('DP1' + o, M, '.', 'R', 'DP2' + o)
        t('DP2' + o, BITS, '.', 'R', 'DP2' + o)
        t('DP2' + o, M, '.', 'R', 'DP3' + o)
        t('DP3' + o, M, '.', 'R', 'DP4' + o)       # C flag: decider run
    t('DP31', BITS, M, 'R', 'VA2')              # verifier accepted: truth 1
    t('DP30', BITS, '.', 'R', 'VN1')            # verifier rejected: C -= 1
    t('VA2', ALL, '1', 'R', 'VA3')
    t('VA3', NB, B, 'R', 'VA3')
    t('VA3', B, '.', 'L', 'VA4')
    t('VA4', B, '.', 'L', 'VA4')
    t('VA4', NB, '.', 'R', 'FB')
    t('FB', B, M, 'R', 'GRB')                   # M_3, then the fuel
    t('VN1', BITS, '.', 'R', 'VN1')
    t('VN1', M, '.', 'L', 'VN2')
    t('VN2', '0', '1', 'L', 'VN2')
    t('VN2', '1', '0', 'R', 'VFE')
    t('VN2', M, '.', 'R', 'VU2')                # underflow: truth 0
    t('VU2', BITS, M, 'R', 'VA3')
    t('VFE', NB, '.', 'R', 'VFE')
    t('VFE', B, '.', 'L', 'FE')
    t('FE', BITS, B, 'L', 'FE')
    t('FE', M, B, 'L', 'FE2')
    t('FE2', BITS, B, 'L', 'FE')
    t('FE2', M, '.', 'R', 'GRB')
    # decider run: compare with the truth flag
    t('DP41', '1', '.', 'L', 'EAs')
    t('DP41', M, '.', 'L', 'BEEP')
    t('DP40', '1', '.', 'L', 'BEEP')
    t('DP40', M, '.', 'L', 'EAs')
    t('BEEP', M, B, 'R', 'EAj')
    m.beep = 'BEEP'
    for x, nxt in (('s', 'SINC'), ('j', 'JE3')):
        t('EA' + x, NB, B, 'R', 'EA' + x)
        t('EA' + x, B, '.', 'L', 'EB' + x)
        t('EB' + x, B, '.', 'L', 'EB' + x)
        t('EB' + x, M, B, 'L', nxt)
    t('JE3', BITS, B, 'L', 'JE3')
    t('JE3', M, '.', 'L', 'JINC')
    # s++ / J++ (shortlex), then a new instance
    for f, ov in (('SINC', 'SOV'), ('JINC', 'JOV')):
        t(f, '1', '0', 'L', f)
        t(f, '0', '1', 'R', 'GRB')
        t(f, M, '.', 'R', ov)
    t('SOV', '0', '.', 'R', 'SOV')
    t('SOV', B, '0', 'R', 'GRB')
    t('JOV', '0', '.', 'R', 'JOV')
    t('JOV', M, '0', 'R', 'JOV2')
    t('JOV2', B, M, 'R', 'GRB')
    # ---------------- BLK: append  M 1^(|s|+1)  at the far right ----------------
    t('GRB', NB, '.', 'R', 'GRB')
    t('GRB', B, M, 'L', 'BN1')
    t('BN1', NB, '.', 'L', 'BN1')
    t('BN1', B, '.', 'R', 'BN2')
    t('BN2', BITS, '.', 'R', 'BN2')
    t('BN2', M, '.', 'R', 'BN3')
    t('BN3', BITS, '.', 'R', 'BN3')
    t('BN3', M, '.', 'R', 'COPY')
    for b in BITS:
        t('COPY', b, B, 'R', 'CR' + b)
        t('CR' + b, NB, '.', 'R', 'CR' + b)
        t('CR' + b, B, '1', 'L', 'CL' + b)
        t('CL' + b, NB, '.', 'L', 'CL' + b)
        t('CL' + b, B, b, 'R', 'COPY')
    t('COPY', M, '.', 'R', 'CX')
    t('CX', NB, '.', 'R', 'CX')
    t('CX', B, '1', 'L', 'BD1')
    # which BLK was that?  C build / verifier fuel / decider fuel
    t('BD1', NB, '.', 'L', 'BD1')
    t('BD1', B, '.', 'R', 'BD2')
    for a, b in (('BD2', 'BD3'), ('BD3', 'BD4'), ('BD4', 'BD5')):
        t(a, BITS, '.', 'R', a)
        t(a, M, '.', 'R', b)
    t('BD5', M, '.', 'L', 'DW1')
    t('BD5', BITS, '.', 'R', 'BD6')
    t('BD6', BITS, '.', 'R', 'BD6')
    t('BD6', B, M, 'R', 'GRB')                  # C built: M_3 + verifier fuel
    t('BD6', M, '.', 'L', 'VG1')                # verifier fuel built
    # decider fuel: one block per position of a walker M moving through J
    t('DW1', NB, '.', 'L', 'DW1')
    t('DW1', B, '.', 'R', 'DW2')
    t('DW2', BITS, '.', 'R', 'DW2')
    t('DW2', M, '.', 'R', 'DW3')
    t('DW3', M, '.', 'L', 'WB1')
    t('WB1', M, '.', 'L', 'WB2')
    t('WB2', B, M, 'R', 'DG2')                  # walker home: write H
    for j in BITS:
        t('DW3', j, M, 'L', 'DW4' + j)
        t('DW4' + j, M, j, 'R', 'GRB')
        t('WB2', j, M, 'R', 'WB3' + j)
        t('WB3' + j, M, j, 'L', 'WB1')
    t('DG2', M, '.', 'R', 'DG3')
    t('DG3', BITS, '.', 'R', 'DG3')
    t('DG3', M, '.', 'R', 'GC')
    # verifier guest source is C
    t('VG1', NB, '.', 'L', 'VG1')
    t('VG1', B, M, 'R', 'VG2')
    t('VG2', M, '.', 'R', 'VG3')
    t('VG3', BITS, '.', 'R', 'VG3')
    t('VG3', M, '.', 'R', 'DG3')
    # ---------------- run setup: guest, then Q = code + '0' ----------------
    for b in BITS:
        t('GC', b, B, 'L', 'GL' + b)
        t('GL' + b, NB, '.', 'L', 'GL' + b)
        t('GL' + b, B, b, 'R', 'GR' + b)
        t('GR' + b, NB, '.', 'R', 'GR' + b)
        t('GR' + b, B, b, 'R', 'GC')
    # end of the guest source: push a separator M (it becomes the gap), then
    # copy the code field right to left into Q
    t('GC', M, B, 'L', 'GLM')
    t('GLM', NB, '.', 'L', 'GLM')
    t('GLM', B, M, 'R', 'GRM')
    t('GRM', NB, '.', 'R', 'GRM')
    t('GRM', B, M, 'L', 'QN2')
    t('QN2', BITS, '.', 'L', 'QN2')
    t('QN2', M, '.', 'L', 'QC')
    for b in BITS:
        t('QC', b, B, 'L', 'QL' + b)
        t('QL' + b, NB, '.', 'L', 'QL' + b)
        t('QL' + b, B, b, 'R', 'QR' + b)
        t('QR' + b, NB, '.', 'R', 'QR' + b)
        t('QR' + b, B, b, 'L', 'QC')
    t('QC', M, '.', 'L', 'QE')
    t('QE', NB, '.', 'L', 'QE')
    t('QE', B, '0', 'R', 'QE3')                 # sentinel
    t('QE3', BITS, '.', 'R', 'QE3')
    t('QE3', M, B, 'L', 'TW')                   # separator -> gap; one rotation
    # ---------------- start ----------------
    t('I0', B, M, 'R', 'I1')
    t('I1', B, M, 'R', 'GRB')
