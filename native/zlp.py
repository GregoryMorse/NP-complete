"""Native machine for L = P (reference: ref/zmh_ref.py).

Built from the zp2 interpreter with the guest tape replaced by the multihead
read-only input of zmh.py (both runs use it).  Changes to zp2:

* Tape between runs as in zp2:  M_g J M_1 s M_2 C M_3 fuel.  C = 1^(|s|+1)
  is only a flag (verifier run) and the counter that builds the verifier's
  heads; there is a single verifier run (program s on input s, |s|+1 heads,
  T = |s|+1), whose outcome is the truth.
* Units are appended at the far right: for the verifier one per cell of C
  (consumed to 0s), for the decider one when the walker reaches M_1 and one
  per step of the walk back through J.  After each unit the head returns to
  the far left and reads the field after M_2 (UD): M is the decider's truth
  flag, a bit is C.
"""
import zp2
import zmh

B, M = 'B', 'M'
BITS = '01'
NB = '01M'

DROP = {'PUTH', 'WC0', 'WC1', 'A', 'BB', 'BB2', 'Y0', 'Y1', 'RGQ1', 'EL1', 'GL0', 'GL1',
        'GR0', 'GR1', 'GC', 'GLM', 'VN1', 'VN2', 'VFE', 'VF2', 'VU2', 'WB1'}


def build():
    m = zp2.build()
    redo = {('QE3', M), ('DP30', '0'), ('DP30', '1'), ('BD6', M), ('DW3', M),
            ('WB30', M), ('WB31', M), ('DG3', M)}
    for w in BITS:
        redo.add(('GHH' + w, M))
        for d in BITS:
            redo.add(('GH' + w + d, M))
    # cells that cannot occur here: no guest cells beyond c, C is all 0s
    # when the verifier halts
    redo |= {('EL2', '0'), ('EL2', '1'), ('GQ1', '0'), ('GQ1', '1'), ('PK1', '0'), ('PK1', '1'),
             ('DP31', '1'), ('VA2', '1'), ('ER20', '0'), ('ER20', '1'), ('ER21', '0'),
             ('ER21', '1')}
    for k in [k for k in m.d if k[0] in DROP or k in redo]:
        del m.d[k]
    t = m.t
    for w in BITS:
        for d in BITS:
            t('GH' + w + d, M, '.', 'R', 'G2' + w + d)
    zmh.act(t)
    zmh.halt(t)
    zmh.units(t, 'UF1')
    zmh.setup(t)
    t('DG3', M, '.', 'R', 'GCD')
    # verifier: one run, outcome = truth
    t('DP30', '0', M, 'R', 'VA3')
    # units for the verifier: one per cell of C
    t('BD6', M, '.', 'L', 'UCL')                    # verifier fuel built
    t('UCL', '1', '.', 'L', 'UCL')
    t('UCL', M, '.', 'R', 'UD')
    t('UF1', BITS, '.', 'R', 'UF1')
    t('UF1', M, '.', 'R', 'UF2')
    t('UF2', BITS, '.', 'R', 'UF2')
    t('UF2', M, '.', 'R', 'UF3')
    t('UF3', BITS, '.', 'R', 'UF3')
    t('UF3', M, '.', 'R', 'UD')
    t('UD', '1', '0', 'R', 'U0')
    t('UD', '0', '.', 'R', 'UD2')
    t('UD', M, '.', 'L', 'UDL')                     # decider: back to the walker
    t('UD2', '0', '.', 'R', 'UD2')
    t('UD2', '1', '0', 'R', 'U0')
    t('UD2', M, '.', 'L', 'VG1')                    # C used up: run the verifier
    t('UDL', NB, '.', 'L', 'UDL')
    t('UDL', B, '.', 'R', 'UDW')
    return m


if __name__ == '__main__':
    print(len(build().states()), 'logical states')
