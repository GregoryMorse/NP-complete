import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
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
    print(txt.split(':=')[0].split('\n')[1][:500])


add('uvFr', 'Charge: one token consumed, sweep to `DEC1`.',
    {'T': 'bits', 'X0': 'NB'},
    ('U', [], ['@b', 'T', 1, 1, 'X0'], False), 'DEC1', cases={'@b': [2, 3]})
add('fbPk', 'Charge: back from the fuel to the tokens.',
    {'T': 'bits', 'W': 'ALL'},
    ('FBACK', [1, 'T', 0], ['W'], True), 'PK1')
add('pkNext', 'Charge: next token.',
    {'T': 'bits', 'W': 'ALL'},
    ('PK1', [1, '@b', 'T', 0], ['W'], True), 'U', cases={'@b': [2, 3]})
add('pkLast', 'Charge: last token done.',
    {'W': 'ALL'},
    ('PK1', [1, 0], ['W'], True), 'U')
open('/tmp/claude-0/sp/segs6.lean', 'w').write('\n'.join(out))
for f in fails:
    print('FAIL', f)
