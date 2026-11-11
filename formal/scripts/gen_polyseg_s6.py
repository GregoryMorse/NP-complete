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


add('uvFr', 'Charge: a token goes to `M_t`, sweep right to the fuel.',
    {'Z': 'ALL', 'T': 'bits', 'X0': 'NB'},
    ('U', ['Z'], ['@b', 'T', 0, 'X0'], False), 'DEC1', cases={'@b': [2, 3]})
add('uvFrH', 'Charge: first token, the gap is still `H`.',
    {'Z': 'ALL', 'T': 'bits', 'X0': 'NB'},
    ('U', ['Z'], ['@b', 'T', 1, 'X0'], False), 'DEC1', cases={'@b': [2, 3]})
add('fbU', 'Charge: back from the fuel, `M_t` moves one token right.',
    {'Z': 'ALL', 'T': 'bits', 'X': 'NB', 'W': 'ALL'},
    ('FBACK', ['Z', 1, '@b', 'T', 0, 'X'], ['W'], True), 'U', cases={'@b': [2, 3]})
add('fbUlast', 'Charge: back from the fuel, no token is left.',
    {'Z': 'ALL', 'X': 'NB', 'W': 'ALL'},
    ('FBACK', ['Z', 1, 0, 'X'], ['W'], True), 'U')
add('uEnd', 'Charge done: `U` meets the gap and writes `H`.',
    {'Z': 'ALL', 'X': 'NB'},
    ('U', ['Z'], [0, 'X'], False), 'DG2')
open(os.path.join(OUT, 'segs6.lean'), 'w').write('\n'.join(out))
for f in fails:
    print('FAIL', f)
