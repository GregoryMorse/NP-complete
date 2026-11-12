"""Native machine for promise-P = promise-BPP (reference: ref/zbpp_ref.py).

Built from zp2 with an accept counter A and a reject counter R after C:

    M_g J M_1 s M_2 C M_3 A M_4 R M_5 fuel

A and R start at ceil(3N/4) - 1 with N = 2^(|s|+1): 1^(|s|+1) with the second
cell (if any) turned 0.  An accepting certificate decrements A, a rejecting
one decrements R, then C is decremented as in zp2.  A borrow out of A's
leading bit (the ceil(3N/4)-th accept) gives truth 1, one out of R truth 0.
If C underflows first, s is outside the promise: everything right of M_2 is
erased and the machine moves to s + 1 without running J.
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
    # accept: decrement A
    drop('DP31', BITS)
    t('DP31', BITS, '.', 'R', 'DPA1')
    t('DPA1', BITS, '.', 'R', 'DPA1')
    t('DPA1', M, '.', 'R', 'DPA2')
    t('DPA2', BITS, '.', 'R', 'DPA2')
    t('DPA2', M, '.', 'L', 'AD')
    t('AD', '0', '1', 'L', 'AD')
    t('AD', '1', '0', 'L', 'ALB')
    t('AD', M, '.', 'L', 'ALC')                 # A underflows: truth 1
    t('ALB', BITS, '.', 'L', 'ALB')
    t('ALB', M, '.', 'L', 'VN2')                # then C -= 1
    t('ALC', BITS, '.', 'L', 'ALC')
    t('ALC', M, '.', 'R', 'VA1')
    t('VA1', BITS, M, 'R', 'VA2')
    # reject: decrement R
    drop('DP30', BITS)
    t('DP30', BITS, '.', 'R', 'DPR1')
    t('DPR1', BITS, '.', 'R', 'DPR1')
    t('DPR1', M, '.', 'R', 'DPR2')
    t('DPR2', BITS, '.', 'R', 'DPR2')
    t('DPR2', M, '.', 'R', 'DPR3')
    t('DPR3', BITS, '.', 'R', 'DPR3')
    t('DPR3', M, '.', 'L', 'RD')
    t('RD', '0', '1', 'L', 'RD')
    t('RD', '1', '0', 'L', 'RLB')
    t('RD', M, '.', 'L', 'RLC')                 # R underflows: truth 0
    t('RLB', BITS, '.', 'L', 'RLB')
    t('RLB', M, '.', 'L', 'ALB')
    t('RLC', BITS, '.', 'L', 'RLC')
    t('RLC', M, '.', 'L', 'RLD')
    t('RLD', BITS, '.', 'L', 'RLD')
    t('RLD', M, '.', 'R', 'VU2')
    t('VU2', '0', M, 'R', 'VA3')
    # C underflow: outside the promise, skip J
    drop('VN2', M)
    t('VN2', M, '.', 'R', 'EAs')
    # refill after C -= 1: skip A and R
    drop('VFE', M)
    t('VFE', M, '.', 'R', 'VFA')
    t('VFA', BITS, '.', 'R', 'VFA')
    t('VFA', M, '.', 'R', 'VFR')
    t('VFR', BITS, '.', 'R', 'VFR')
    t('VFR', M, '.', 'R', 'VF2')
    # BLK copy: the fixed counters contain 0s
    t('CX', '0', '.', 'R', 'CX')
    # BLK dispatch: C built -> build A -> build R -> build the verifier fuel
    drop('BD6', M + B)
    t('BD6', B, M, 'L', 'BN1')                  # C built: M_3 opens A
    t('BD6', M, '.', 'R', 'BD7')
    t('BD7', BITS, '.', 'R', 'BD7')
    t('BD7', B, M, 'L', 'FXA')                  # A built: M_4, fix A, build R
    t('BD7', M, '.', 'R', 'BD8')
    t('BD8', BITS, '.', 'R', 'BD8')
    t('BD8', B, M, 'L', 'FXR')                  # R built: M_5, fix R, verifier fuel
    t('BD8', M, '.', 'L', 'VG1')
    for X, nxt in (('A', 'BN1'), ('R', 'GRB')):
        t('FX' + X, '1', '.', 'L', 'FX' + X)
        t('FX' + X, M, '.', 'R', 'FX%s1' % X)
        t('FX%s1' % X, '1', '.', 'R', 'FX%s2' % X)
        t('FX%s2' % X, '1', '0', 'L' if nxt == 'BN1' else 'R', nxt)
        t('FX%s2' % X, M, '.', 'L' if nxt == 'BN1' else 'R', nxt)
    return m
