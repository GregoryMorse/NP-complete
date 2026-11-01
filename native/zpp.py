"""Native machine for P = PP (reference: ref/zpp_ref.py).

Built from zp2 with an accept counter A after C:

    M_g J M_1 s M_2 C M_3 A M_4 fuel

A = 1^(|s|+1) is decremented at every accepting certificate; its leading
bit turns 0 exactly at the 2^|s|-th accept, which is the 'at least half'
threshold (truth 1).  If C underflows first, truth is 0.
"""
import zp2

B, M = 'B', 'M'
BITS = '01'


def build():
    m = zp2.build()
    t = m.t

    def drop(q, syms):
        for a in syms:
            del m.d[(q, a)]
    # accept: decrement A, then C
    drop('DP31', BITS)
    t('DP31', BITS, '.', 'R', 'DPA1')
    t('DPA1', BITS, '.', 'R', 'DPA1')
    t('DPA1', M, '.', 'R', 'DPA2')
    t('DPA2', BITS, '.', 'R', 'DPA2')
    t('DPA2', M, '.', 'L', 'AD')
    t('AD', '0', '1', 'L', 'AD')
    t('AD', '1', '0', 'L', 'ACHK')
    t('ACHK', BITS, '.', 'L', 'ALB')           # not the leading bit: C -= 1
    t('ACHK', M, '.', 'L', 'ALC')              # leading bit flipped: truth 1
    t('ALB', BITS, '.', 'L', 'ALB')
    t('ALB', M, '.', 'L', 'VN2')
    t('ALC', BITS, '.', 'L', 'ALC')
    t('ALC', M, '.', 'R', 'VA1')
    t('VA1', BITS, M, 'R', 'VA2')
    # refill after C -= 1: skip A
    drop('VFE', M)
    t('VFE', M, '.', 'R', 'VFA')
    t('VFA', BITS, '.', 'R', 'VFA')
    t('VFA', M, '.', 'R', 'VF2')
    # BLK dispatch: C built -> build A -> build the verifier fuel
    drop('BD6', M + B)
    t('BD6', B, M, 'L', 'BN1')                 # C built: M_3 opens A (BLK)
    t('BD6', M, '.', 'R', 'BD7')
    t('BD7', '1', '.', 'R', 'BD7')
    t('BD7', B, M, 'R', 'GRB')                 # A built: M_4 + verifier fuel
    t('BD7', M, '.', 'L', 'VG1')
    return m
