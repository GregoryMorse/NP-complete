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


VS = {'Z': 'ALL', 'Kr': 'bits', 'X': 'NB'}
add('j2End', 'K + 1 (a `0` became `1`): skip to `M_1`, erase everything right of it, write `M_a`.', VS,
    ('J2', ['Z'], ['Kr', 1, '@b', 'X'], False), 'GRB', cases={'@b': [1, 2, 3]})
add('jov2End', 'K + 1 (carry out): `M_1` moves right, erase the rest, write `M_a`.', {'Z': 'ALL', 'X': 'NB'},
    ('JOV2', ['Z'], ['@b', 'X'], False), 'GRB', cases={'@b': [1, 2, 3]})
add('kinc0', 'K + 1: a `0` becomes `1`.', VS,
    ('KINC', ['Z'], [2, 'Kr', 1, '@b', 'X'], False), 'GRB', cases={'@b': [1, 2, 3]})
add('kincOv', 'K + 1: the carry leaves `K`.', {'Z': 'ALL', 'X': 'NB'},
    ('KINC', ['Z'], [1, '@b', 'X'], False), 'GRB', cases={'@b': [1, 2, 3]})
add('kinc1', 'K + 1: a `1` becomes `0`, carry.', {'Z': 'ALL', 'R': 'ALL'},
    ('KINC', ['Z'], [3, 'R'], False), 'KINC')
open(os.path.join(OUT, 'segs10.lean'), 'w').write('\n'.join(out))
for f in fails:
    print('FAIL', f)
