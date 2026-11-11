"""Native machine for L = NL (reference: ref/znl_ref.py).

The verifier runs are zp2's (certificate counter C, guest tape copied from C)
with a one-way head: the action 'write w, move left' becomes 'write w, stay'.
The decider run uses the multihead read-only input of zmh.py.  Changes:

* VG1 writes H one cell further left with a dummy 0 between H and M_g, so
  during a verifier run the cell right of H is always a bit; during a decider
  run it is M_g.  The act (GHwd at H) looks right once (XWwd) and dispatches.
* Decider setup: DG3 -> GCD (zmh.setup); verifier setup: VG3 -> DG3V -> GC
  (zp2's guest copy).  QE4 tells the two apart by the cell right of the gap
  separator (M placeholder for c, or the guest's first cell).
* Units are appended only for the decider (walker), returning straight to the
  walker (UDW).
"""
import zp2
import zmh

B, M = 'B', 'M'
BITS = '01'
NB = '01M'

DROP = {'A', 'BB', 'BB2', 'Y0', 'Y1', 'EL1', 'WB1'}


def build():
    m = zp2.build()
    redo = {('QE3', M), ('DW3', M), ('WB30', M), ('WB31', M), ('DG3', M), ('VG1', B),
            ('VG3', M), ('WC0', B), ('WC1', B)}
    for w in BITS:
        redo.add(('GHH' + w, M))
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
            t('XW' + o, BITS, '.', 'L', 'YW' + o)   # guest cell or dummy: verifier
        t('YW' + w + '1', M, w, 'L', 'PUTH')
        t('YW' + w + '0', M, '.', 'L', 'WC' + w)
        t('WC' + w, B, w, 'L', 'RGQ1')              # one-way: write w and stay
    zmh.act(t)
    zmh.halt(t)
    zmh.units(t, 'UDW')
    zmh.setup(t)
    t('QE4', BITS, '.', 'L', 'TW')                  # verifier: guest cell
    t('DG3', M, '.', 'R', 'GCD')
    t('VG3', M, '.', 'R', 'DG3V')
    t('DG3V', BITS, '.', 'R', 'DG3V')
    t('DG3V', M, '.', 'R', 'GC')
    t('VG1', B, '.', 'L', 'VGD')
    t('VGD', B, M, 'R', 'VGE')                      # H
    t('VGE', B, '0', 'R', 'VG2')                    # dummy
    return m


if __name__ == '__main__':
    print(len(build().states()), 'logical states')
