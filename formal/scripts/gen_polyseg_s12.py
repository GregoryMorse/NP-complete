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


KAS = {'Kr': 'bits', 'a': 'bits', 's': 'bits'}
add('dBad0E', 'Wrong answer (truth flag `1`): erase the fuel, back to `s`.', dict(KAS, Fu='NB'),
    ('EAs', [1, 'Kr', 1, 'a', 1, 's', 1, 2], [3, 1, 'Fu'], False), 'ZS')
open(os.path.join(OUT, 'segs12.lean'), 'w').write('\n'.join(out))
for f in fails:
    print('FAIL', f)
