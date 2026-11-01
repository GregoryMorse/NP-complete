"""Native machine for NP = coNP (reference: ref/zconp_ref.py).

Built from zp2's interpreter.  Changes:

* Fresh cells are nondeterministic.  When the head moves right onto a blank
  cell (PUTH -> PF), the next choice is fetched from D, which sits after the
  fuel behind one blank:  fuel B d_1 .. d_j M d_(j+1) .. d_k.  The pointer M
  moves right past the fetched bit; at the end the choice defaults to 1 and D
  grows.  Choice 1 writes '1' into the fresh cell, choice 0 leaves it blank.
* After a rejecting run D is backtracked (strip trailing 0s, last 1 -> 0) and
  the pointer is shifted back to the front; an emptied D ends the phase with 0.
* Code fields lose their trailing 1s when copied into Q (QS).

Between runs:  M_g J M_1 s M_2 [t] M_3 M B_R .. M B_1 B D
The slot is empty in the verifier phase (code s, empty input, one fuel block)
and holds the truth bit t in the decider phase (code J, input s, |J|+1 blocks).
"""
import zp2
from logic import LTM

B, M = 'B', 'M'
BITS = '01'
NB = '01M'


def build():
    m = zp2.build()
    o = LTM('I0')
    zp2.outer(o)
    for k in list(o.d):
        del m.d[k]
    for k in [k for k in m.d if k[0] in ('RGQ1', 'PUTH')]:
        del m.d[k]
    t = m.t
    # ---------------- interpreter patches ----------------
    t('RGQ1', NB, '.', 'L', 'RGQ1')
    t('RGQ1', B, '.', 'L', 'RTW')
    t('PUTH', B, M, 'L', 'PF')
    t('PF', BITS, '.', 'L', 'RGQ1')
    t('PF', B, '.', 'R', 'FT1')                 # fresh cell: fetch a choice
    t('FT1', NB, '.', 'R', 'FT1')
    t('FT1', B, '.', 'R', 'FT2')
    t('FT2', BITS, '.', 'R', 'FT2')
    t('FT2', M, '.', 'R', 'FT3')
    t('FT2', B, '1', 'R', 'FT3')                # D empty: start it
    t('FT3', '0', M, 'L', 'FTW0')
    t('FT3', '1B', M, 'L', 'FTW1')              # end of D: choice 1, D grows
    for b in BITS:
        t('FTW' + b, M, b, 'L', 'FTW' + b)
        t('FTW' + b, BITS, '.', 'L', 'FTW' + b)
    t('FTW0', B, '.', 'L', 'RGQ1')              # leave the fresh cell blank
    t('FTW1', B, '.', 'L', 'RTC1')
    t('RTC1', NB, '.', 'L', 'RTC1')
    t('RTC1', B, '1', 'L', 'RGQ1')
    # ---------------- result dispatch (head right of M_g) ----------------
    for r in BITS:
        t('DP1' + r, BITS, '.', 'R', 'DP1' + r)
        t('DP1' + r, M, '.', 'R', 'DP2' + r)
        t('DP2' + r, BITS, '.', 'R', 'DP2' + r)
        t('DP2' + r, M, '.', 'R', 'DP3' + r)
    t('DP31', M, '1', 'R', 'EAs')               # verifier accepted: t = 1
    t('DP31', '1', '0', 'R', 'BEEP')            # decider accepted, s in L
    t('DP31', '0', B, 'R', 'EAs')               # decider accepted, s not in L
    t('DP30', NB, '.', 'R', 'BTR1')             # rejected: backtrack D
    t('BTR1', NB, '.', 'R', 'BTR1')
    t('BTR1', B, '.', 'R', 'BTR2')
    t('BTR2', NB, '.', 'R', 'BTR2')
    t('BTR2', B, '.', 'L', 'BT')
    t('BT', M + '0', B, 'L', 'BT')
    t('BT', '1', M, 'R', 'RS0')
    t('BT', B, '.', 'L', 'EX1')                 # D exhausted: result 0
    # shift the pointer back to the front of D
    t('RS0', B, '0', 'L', 'RS2')
    t('RS2', M, '.', 'L', 'RS2')
    for b in BITS:
        t('RS2', b, M, 'R', 'RS' + b)
        t('RS' + b, M, b, 'L', 'RS2')
    t('RS2', B, '.', 'L', 'ER3')
    # erase the fuel and rebuild it (same length, so D stays put)
    t('ER3', BITS, B, 'L', 'ER3')
    t('ER3', M, B, 'L', 'ER4')
    t('ER4', BITS, B, 'L', 'ER3')
    t('ER4', M, '.', 'R', 'GRB')
    # exhausted: erase the fuel leftwards, then the phase result is 0
    t('EX1', BITS, B, 'L', 'EX1')
    t('EX1', M, B, 'L', 'EX2')
    t('EX2', BITS, B, 'L', 'EX1')
    t('EX2', M, '.', 'L', 'EX3')
    t('EX3', M, '.', 'R', 'EX4')                # verifier: t = 0
    t('EX4', M, '0', 'R', 'FB')
    t('EX3', '0', '.', 'R', 'BEEP')             # decider rejected, s not in L
    t('EX3', '1', B, 'R', 'EAs')
    t('BEEP', M, B, 'R', 'EAs')
    m.beep = 'BEEP'
    t('EAs', NB, B, 'R', 'EAs')
    t('EAs', B, '.', 'R', 'EAs2')
    t('EAs2', NB, B, 'R', 'EAs')
    t('EAs2', B, '.', 'L', 'EBs')
    t('EBs', B, '.', 'L', 'EBs')
    t('EBs', '1', '.', 'R', 'FB')               # t = 1 kept: decider phase
    t('FB', B, M, 'R', 'GRB')                   # M_3, then decider fuel
    t('EBs', M, B, 'L', 'SINC')                 # M_2: s++
    t('EBs', '0', B, 'L', 'EBj')                # beep mark: J++
    t('EBj', M, B, 'L', 'JE3')
    t('JE3', BITS, B, 'L', 'JE3')
    t('JE3', M, '.', 'L', 'JINC')
    for f, ov in (('SINC', 'SOV'), ('JINC', 'JOV')):
        t(f, '1', '0', 'L', f)
        t(f, '0', '1', 'R', 'W1')
        t(f, M, '.', 'R', ov)
    t('SOV', '0', '.', 'R', 'SOV')
    t('SOV', B, '0', 'R', 'W1')
    t('JOV', '0', '.', 'R', 'JOV')
    t('JOV', M, '0', 'R', 'JOV2')
    t('JOV2', B, M, 'R', 'W1')
    # new instance: M_2 M_3, then one fuel block
    t('W1', NB, '.', 'R', 'W1')
    t('W1', B, M, 'R', 'FB')
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
    # which block was that?  decided from the right end
    t('BD1', '1', '.', 'L', 'BD1')
    t('BD1', M, '.', 'L', 'BD2')
    t('BD2', BITS, '.', 'L', 'DW1')             # a later decider block
    t('BD2', M, '.', 'L', 'BD3')                # M_3
    t('BD3', M, '.', 'L', 'VG1')                # M_2: verifier fuel built
    t('BD3', BITS, '.', 'L', 'DW1')             # t: first decider block
    t('DW1', NB, '.', 'L', 'DW1')
    t('DW1', B, '.', 'R', 'DW2')
    t('DW2', BITS, '.', 'R', 'DW2')
    t('DW2', M, '.', 'R', 'DW3')
    t('DW3', M, '.', 'L', 'WB1')
    t('WB1', M, '.', 'L', 'WB2')
    t('WB2', B, M, 'R', 'DG2')
    for j in BITS:
        t('DW3', j, M, 'L', 'DW4' + j)
        t('DW4' + j, M, j, 'R', 'GRB')
        t('WB2', j, M, 'R', 'WB3' + j)
        t('WB3' + j, M, j, 'L', 'WB1')
    t('DG2', M, '.', 'R', 'DG3')
    t('DG3', BITS, '.', 'R', 'DG3')
    t('DG3', M, '.', 'R', 'GC')
    t('VG1', NB, '.', 'L', 'VG1')
    t('VG1', B, M, 'R', 'VG2')
    t('VG2', M, '.', 'R', 'VG3')
    t('VG3', BITS, '.', 'R', 'VG3')
    t('VG3', M, '.', 'R', 'DG3')
    # ---------------- run setup: guest, then Q = core(code) + '0' ----------------
    for b in BITS:
        t('GC', b, B, 'L', 'GL' + b)
        t('GL' + b, NB, '.', 'L', 'GL' + b)
        t('GL' + b, B, b, 'R', 'GR' + b)
        t('GR' + b, NB, '.', 'R', 'GR' + b)
        t('GR' + b, B, b, 'R', 'GC')
    t('GC', M, B, 'L', 'GLM')
    t('GLM', NB, '.', 'L', 'GLM')
    t('GLM', B, M, 'R', 'GRM')
    t('GRM', NB, '.', 'R', 'GRM')
    t('GRM', B, M, 'L', 'QN2')
    t('QN2', BITS, '.', 'L', 'QN2')
    t('QN2', M, '.', 'L', 'QS')
    t('QS', '1', '.', 'L', 'QS')                # core: drop trailing 1s
    t('QS', '0', B, 'L', 'QL0')
    t('QS', M, '.', 'L', 'QE')
    for b in BITS:
        t('QC', b, B, 'L', 'QL' + b)
        t('QL' + b, NB, '.', 'L', 'QL' + b)
        t('QL' + b, B, b, 'R', 'QR' + b)
        t('QR' + b, NB, '.', 'R', 'QR' + b)
        t('QR' + b, B, b, 'L', 'QC')
    t('QC', M, '.', 'L', 'QE')
    t('QE', NB, '.', 'L', 'QE')
    t('QE', B, '0', 'R', 'QE3')
    t('QE3', BITS, '.', 'R', 'QE3')
    t('QE3', M, B, 'L', 'TW')
    t('I0', B, M, 'R', 'JOV2')
    return m


if __name__ == '__main__':
    m = build()
    print(len(m.states()), 'logical states')
