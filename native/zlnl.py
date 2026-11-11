"""Native machine for L = NL (reference: ref/znl_ref.py).

The verifier runs are zp2's (certificate counter C, guest tape copied from C)
with a one-way head: the action 'write w, move left' becomes 'write w, stay'.
The decider run uses the multihead read-only input of zmh.py.  Changes:

* VG1 writes H one cell further left with a dummy 0 between H and M_g, so
  during a verifier run the cell right of H is always a bit; during a decider
  run it is M_g.  The act (GHwd at H) looks right once (XWwd) and dispatches.
  The verifier's 'write w, stay' is zmh's WCw (write w into c_h, RGQ1).
* Decider setup: DG3 -> GCD (skip s, mark M_2, zp2's GLM writes c); verifier
  setup: VG3 -> DG3V -> GC (zp2's guest copy).
* Units are appended only for the decider (walker), returning straight to the
  walker (UDW).  The storage is erased after the comparison (EX after EAs).
"""
import zp2
import zmh

B, M = 'B', 'M'
BITS = '01'
NB = '01M'

DROP = {'A', 'BB', 'BB2', 'Y0', 'Y1', 'WB1'}


def build():
    m = zp2.build()
    redo = {('DW3', M), ('WB30', M), ('WB31', M), ('DG3', M), ('VG1', B),
            ('VG3', M), ('WC0', B), ('WC1', B), ('EAs', B)}
    for w in BITS:
        for d in BITS:
            redo.add(('GH' + w + d, M))
    for k in [k for k in m.d if k[0] in DROP or k in redo]:
        del m.d[k]
    t = m.t
    for w in BITS:
        for d in BITS:
            o = w + d
            t('GH' + o, M, '.', 'R', 'XW' + o)
            t('XW' + o, M, '.', 'R', 'G2' + o)      # M_g: decider
        # guest cell or dummy: verifier.  d = 1 as in zp2; d = 0 (one-way):
        # write w into c_h and stay (zmh's WCw skips H)
        t('XW' + w + '1', BITS, '.', 'L', 'YW' + w)
        t('YW' + w, M, w, 'L', 'PUTH')
        t('XW' + w + '0', BITS, '.', 'L', 'WC' + w)
    zmh.act(t)
    zmh.units(t, 'UDW')
    zmh.erase(t, 'EAs', 'EBs', 'EX')
    t('DW3', M, '.', 'R', 'U0')
    for j in BITS:
        t('WB3' + j, M, j, 'R', 'U0')
    t('UDW', BITS, '.', 'R', 'UDW')
    t('UDW', M, '.', 'L', 'WB2')
    t('DG3', M, '.', 'R', 'GCD')
    t('GCD', BITS, '.', 'R', 'GCD')
    t('GCD', M, B, 'L', 'GLM')                      # mark M_2: code J
    t('VG3', M, '.', 'R', 'DG3V')
    t('DG3V', BITS, '.', 'R', 'DG3V')
    t('DG3V', M, '.', 'R', 'GC')
    t('VG1', B, '.', 'L', 'VGD')
    t('VGD', B, M, 'R', 'VGE')                      # H
    t('VGE', B, '0', 'R', 'VG2')                    # dummy
    return m


if __name__ == '__main__':
    print(len(build().states()), 'logical states')
