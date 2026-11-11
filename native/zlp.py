"""Native machine for L = P (reference: ref/zmh_ref.py).

Built from the zp2 interpreter with the guest tape replaced by the multihead
read-only input of zmh.py (both runs use it).  Changes to zp2:

* Tape between runs as in zp2:  M_g J M_1 s M_2 C M_3 fuel.  C = 1^(|s|+1)
  is only a flag (verifier run) and the counter of the verifier's heads; there
  is a single verifier run (program s on input s, |s|+1 heads, T = |s|+1),
  whose outcome is the truth.
* Units are appended at the far right: for the decider one when the walker
  reaches M_1 and one per step of the walk back through J, for the verifier
  one per cell of C (consumed to 0s).  After each unit the head returns to
  the walker (UDW); the walk back ends at home without writing H (WB2), and
  then GCD looks at the field after M_2 (GC2): a bit is C (append the next
  verifier unit, or set up the verifier run once C is all 0s), M is the
  decider's truth flag.
* Run setup: GLMD writes H, zp2's GLM the placeholder for c, then zp2's code
  copy (GRM .. QE3).
* The storage is erased with the rest at the far right (EX after EAs, EY
  after VA3).
"""
import zp2
import zmh

B, M = 'B', 'M'
BITS = '01'
NB = '01M'

DROP = {'PUTH', 'A', 'BB', 'BB2', 'Y0', 'Y1', 'GL0', 'GL1', 'GR0', 'GR1', 'GC',
        'VN1', 'VN2', 'VFE', 'VF2', 'VU2', 'WB1', 'VG1', 'VG2', 'VG3'}


def build():
    m = zp2.build()
    redo = {('DP30', '0'), ('DP30', '1'), ('BD6', M), ('DW3', M), ('WB30', M), ('WB31', M),
            ('WB2', B), ('DG3', M), ('WC0', B), ('WC1', B), ('EAs', B), ('VA3', B)}
    for w in BITS:
        for d in BITS:
            redo.add(('GH' + w + d, M))
    # cells that cannot occur here: no guest cells beyond c, H next to M_g,
    # C is all 0s when the verifier halts
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
    zmh.units(t, 'UDW')
    zmh.erase(t, 'EAs', 'EBs', 'EX')
    zmh.erase(t, 'VA3', 'VA4', 'EY')
    # decider units: walker at M_1, then one per step back
    t('DW3', M, '.', 'R', 'U0')
    for j in BITS:
        t('WB3' + j, M, j, 'R', 'U0')
    t('UDW', BITS, '.', 'R', 'UDW')
    t('UDW', M, '.', 'L', 'WB2')
    t('WB2', B, '.', 'R', 'DG2')                    # home (no H yet)
    t('BD6', M, '.', 'L', 'UL2')                    # verifier fuel built
    t('DG3', M, '.', 'R', 'GCD')
    t('GCD', BITS, '.', 'R', 'GCD')
    t('GCD', M, '.', 'R', 'GC2')
    t('GC2', M, '.', 'L', 'GC4')                    # decider: mark M_2, code J
    t('GC2', '1', '0', 'R', 'U0')                   # verifier unit
    t('GC2', '0', '.', 'R', 'GC4')
    t('GC4', '0', '.', 'R', 'GC4')
    t('GC4', '1', '0', 'R', 'U0')
    t('GC4', M, B, 'L', 'GLMD')                     # C used up: code s
    t('GLMD', NB, '.', 'L', 'GLMD')
    t('GLMD', B, M, 'L', 'GLM')                     # H, then GLM: c
    # verifier: one run, outcome = truth
    t('DP30', '0', M, 'R', 'VA3')
    return m


if __name__ == '__main__':
    print(len(build().states()), 'logical states')
