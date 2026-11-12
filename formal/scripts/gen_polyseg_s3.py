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
L1 = [1, 'Kr', 1, 'a', 1, 's']
add('vAcc', 'Verifier accepted: truth flag `1`.', dict(KAS, Y='NB'),
    ('DP11', [1], ['Kr', 1, 'a', 1, 's', 1, '@c', '@y', 'Y'], False), 'GRB',
    cases={'@c': [2, 3], '@y': [1, 2, 3]})
add('vRejE', 'Verifier rejected: `C -= 1`, refill the fuel, run again.', dict(KAS, Z='Z2', D='T3', E='Z2'),
    ('DP10', [1], ['Kr', 1, 'a', 1, 's', 1, 3, 'Z', 1, 1, 'D', 'E'], False), 'GC')
add('vRejC', 'Verifier rejected, `C` has more bits.', dict(KAS, Cp='bits', Z='Z2', D='T3', E='Z2'),
    ('DP10', [1], ['Kr', 1, 'a', 1, 's', 1, '@c', 'Cp', 3, 'Z', 1, 1, 'D', 'E'], False), 'GC',
    cases={'@c': [2, 3]})
add('vUnder', 'Verifier rejected at `C = 0`: truth flag `0`.', dict(KAS, Z='Z2', Fu='NB'),
    ('DP10', [1], ['Kr', 1, 'a', 1, 's', 1, 2, 'Z', 1, 'Fu'], False), 'GRB')
add('dOk1', 'dok1', dict(KAS, Fu='NB'),
    ('DP11', [1], ['Kr', 1, 'a', 1, 's', 1, 1, 3, 1, 'Fu'], False), 'SINC')
add('dOk0', 'dok0', dict(KAS, Fu='NB'),
    ('DP10', [1], ['Kr', 1, 'a', 1, 's', 1, 1, 1, 'Fu'], False), 'SINC')
add('dBad1', 'dbad1', dict(KAS, Fu='NB'),
    ('DP11', [1], ['Kr', 1, 'a', 1, 's', 1, 1, 1, 'Fu'], False), 'BEEP')
add('dBad0', 'dbad0', dict(KAS, Fu='NB'),
    ('DP10', [1], ['Kr', 1, 'a', 1, 's', 1, 1, 3, 1, 'Fu'], False), 'BEEP')
add('dBad1E', 'dbad1E', dict(KAS, Fu='NB'),
    ('EAs', [1, 'Kr', 1, 'a', 1, 's', 1, 2], [1, 'Fu'], False), 'ZS')
open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), 'out', 'segs3.lean'), 'w').write('\n'.join(out))
for f in fails:
    print('FAIL', f)
