import sys
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import gen_polyseg_gen as gen
import symexec as S
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
    print(txt.split(':=')[0].split('\n')[1][:400])


add('chargeStart', 'Charge: blank `M_a`, go back to the first bit of `a`.', {'K': 'bits', 'a': 'bits', 'Y': 'ALL'},
    ('CHS', [1], [1, 'K', 1, 'a', 1, 'Y'], False), 'GC')
add('gcBodyC', 'Charge copy of `a` as tokens: one bit to the far left.',
    {'Ur': 'bits', 'V': 'NB', 'P': 'bits', 'u': 'bits', 'v': 'bits', 'Rest': 'ALL'},
    ('GC', ['Ur', 1, 'V', 'P', 1, 'u'], ['@b', 'v', 0, 'Rest'], False), 'GC', cases={'@b': [2, 3]})
add('gcEndC', 'Charge copy done: `M_a` back, to the first token.',
    {'Ur': 'bits', 'V': 'NB', 'P': 'bits', 'u': 'bits', 'Rest': 'ALL'},
    ('GC', ['Ur', 1, 'V', 'P', 1, 'u'], [0, 'Rest'], False), 'U')
open('/tmp/claude-0/sp/segs5.lean', 'w').write('\n'.join(out))
for f in fails:
    print('FAIL', f)
