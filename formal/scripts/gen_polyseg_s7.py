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
    print(txt.split(':=')[0].split('\n')[1][:500])


add('exhCharge', 'Charge exhausts the fuel: `M_g` becomes `0`, the tokens are erased, `M_g` is restored, `K + 1` starts.',
    {'Z': 'ALL', 'T': 'bits', 'Y': 'NB', 'W': 'ALL'},
    ('EXH', ['Z', 1, 'T', 0], [1, 'Y', 1, 'W'], True), 'BEEPX')
add('exhCharge0', 'Charge exhausts the fuel with no token left.',
    {'Z': 'ALL', 'Y': 'NB', 'W': 'ALL'},
    ('EXH', ['Z', 1, 0], [1, 'Y', 1, 'W'], True), 'BEEPX')
open(os.path.join(OUT, 'segs7.lean'), 'w').write('\n'.join(out))
for f in fails:
    print('FAIL', f)
