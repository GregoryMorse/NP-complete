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


add('uMEnd', 'Charge of an empty `a`: `U` meets `H` and passes it.',
    {'Z': 'ALL', 'X': 'NB'},
    ('U', ['Z'], [1, 'X'], False), 'DG2')
open(os.path.join(OUT, 'segs8.lean'), 'w').write('\n'.join(out))
for f in fails:
    print('FAIL', f)
