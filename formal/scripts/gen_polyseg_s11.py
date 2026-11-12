import sys
import os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_polyseg_gen as gen
OUT = os.path.join(HERE, 'out')
os.makedirs(OUT, exist_ok=True)
out = []
fails = []


def add(*a, **k):
    try:
        txt, ks = gen.seg(*a, **k)
    except Exception as e:
        fails.append((a[0], str(e)[:300]))
        return
    out.append(txt)
    print(a[0], ks)
    print(txt.split(':=')[0][:600])


add('zsSweep', 'Wrong answer: `s := 0^n`, back to the last cell of `a`.', {'Z': 'ALL', 's': 'bits'},
    ('ZS', ['Z', 1, 's'], [], True), 'SINC')
add('cOvA', 'Correct, `s` all ones: the carry reaches `M_a`, a `0` is appended, back to `a`.',
    {'Z': 'ALL', 'N': 'Z2'},
    ('SINC', ['Z', 1], ['N'], True), 'DL1')
add('dlStep', 'Overflow: one cell of `a` moves to `s`.', {'Z': 'ALL', 'N': 'Z2'},
    ('DL1', ['Z', '@b'], [1, 'N', 2], True), 'DL1', cases={'@b': [2, 3]})
add('dlEnd', 'Overflow: `a` is empty.', {'Z': 'ALL', 'N': 'Z2'},
    ('DL1', ['Z', 1], [1, 'N', 2], True), 'GRB')
add('wOv0', 'Wrong, `a` all ones: `a` grows, `s` empty.', {'Z': 'ALL', 'N': 'Z2'},
    ('SINC', ['Z', 1], ['N', 1], True), 'GRB')
add('wOv1', 'Wrong, `a` all ones: `a` grows, `s` is kept at length `n`.', {'Z': 'ALL', 'N': 'Z2', 'S': 'Z2'},
    ('SINC', ['Z', 1], ['N', 1, 2, 'S'], True), 'GRB')
open(os.path.join(OUT, 'segs11.lean'), 'w').write('\n'.join(out))
for f in fails:
    print('FAIL', f)
