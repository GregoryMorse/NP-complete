import sys
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import gen_polyseg_gen as gen
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
add('blk1Start', 'First `BLK` (the certificate counter): `M_2` at the end, back to the first bit of `s`.', KAS,
    ('GRB', [1, 'Kr', 1, 'a', 1, 's'], [], False), 'COPY')
add('copyBody1', 'One `COPY` round of the first `BLK`.', {'P': 'NB', 'u': 'bits', 'v': 'bits'},
    ('COPY', ['P', 'u'], ['@b', 'v', 1, ('u', 3)], False), 'COPY', cases={'@b': [2, 3]})
add('blk1End0', 'First `BLK` done, `s = []`: `C = 1`, `M_3`.', KAS,
    ('COPY', [1, 'Kr', 1, 'a', 1, 's'], [1], False), 'GRB')
add('blk1End1', 'First `BLK` done, `s` nonempty: `C`, `M_3`.', dict(KAS, C0='T3'),
    ('COPY', [1, 'Kr', 1, 'a', 1, 's'], [1, 3, 'C0'], False), 'GRB')
add('blkDecStep', 'Decider fuel block done, the walker steps right.',
    {'Kl': 'bits', 'Kr': 'bits', 'a': 'bits', 's': 'bits', 't': 'T3', 'Bl': 'O13'},
    ('COPY', ['Kl', 1, '@b', 'Kr', 1, 'a', 1, 's'], [1, 1, 't', 1, 'Bl', 1, ('s', 3)], False), 'GRB',
    cases={'@b': [2, 3]})
add('blkDecLast', 'Last decider fuel block: the walker goes home.',
    {'Kl': 'bits', 'a': 'bits', 's': 'bits', 't': 'T3', 'Bl': 'O13'},
    ('COPY', ['Kl', 1, 1, 'a', 1, 's'], [1, 1, 't', 1, 'Bl', 1, ('s', 3)], False), 'WB1')
add('wbEnd', 'The walker is home: `H`, start of the charge.', {'K': 'bits', 'Y': 'ALL'},
    ('WB1', [1], ['K', 1, 'Y'], True), 'CHS')
add('sinc0', 'Increment: a `0` becomes `1`.', {'A': 'NB', 'r': 'bits', 'Z': 'NB'},
    ('SINC', ['A', 1, 'r', 2], ['Z'], True), 'GRB')
add('sinc1', 'Increment: a `1` becomes `0`, carry.', {'A': 'NB', 'r': 'bits', 'Z': 'NB'},
    ('SINC', ['A', 1, 'r', 3], ['Z'], True), 'SINC')
open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), 'out', 'segs4.lean'), 'w').write('\n'.join(out))
for f in fails:
    print('FAIL', f)
