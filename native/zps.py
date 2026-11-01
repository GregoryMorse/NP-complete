"""Native machine for P = PSPACE (reference: ref/zps_ref.py).

Built from zp2.  The certificate counter C walks the quantifier game tree
depth first (first child c_i = 1) with short-circuiting, so no value stack is
needed.  After a verifier run with result r the walk goes left from C's last
bit, level parity alternating (EXISTS at the last bit):
  0  : that node's second child is done; set the bit to 1 and go up.
  1  : first child done.  If r is the node's dominant value (1 for EXISTS,
       0 for FORALL) go up; else write 0 (start the second child) and run.
  M_2: the root has value r.
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
    for o in BITS:
        drop('DP3' + o, BITS)
        t('DP3' + o, BITS, '.', 'R', 'DPV' + o)
        t('DPV' + o, BITS, '.', 'R', 'DPV' + o)
        t('DPV' + o, M, '.', 'L', 'WK%sE' % o)
    for r in BITS:
        for q, q2, dom in (('E', 'A', '1'), ('A', 'E', '0')):
            k = 'WK%s%s' % (r, q)
            t(k, '0', '1', 'L', 'WK%s%s' % (r, q2))
            if r == dom:
                t(k, '1', '.', 'L', 'WK%s%s' % (r, q2))
            else:
                t(k, '1', '0', 'R', 'VFE')
            t(k, M, '.', 'R', 'VA1' if r == '1' else 'VU2')
    t('VA1', '1', M, 'R', 'VA2')
    for q in ('VN1', 'VN2'):
        for a in 'BM01':
            m.d.pop((q, a), None)
    return m
