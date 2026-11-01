"""Run one instance (J, s) of a logical machine from tape 'M J M s', state
GRB, until it reaches s++ (SINC: J correct) or BEEP (J wrong)."""
import random, sys
sys.path.insert(0, '../ref')
import zp2_ref
from itertools import product

def instance(m, J, s, maxsteps=50_000_000):
    tape = {i: c for i, c in enumerate('M' + J + 'M' + s)}
    h = len(J) + len(s) + 2; q = 'GRB'
    for _ in range(maxsteps):
        tr = m.d.get((q, tape.get(h, 'B')))
        if tr is None:
            return ('undef', q, tape.get(h, 'B'))
        tape[h], mv, q = tr
        h += 1 if mv == 'R' else -1
        if q == 'SINC': return True
        if q == m.beep: return False
    return 'steps'

def check(m, truth, trials=60, seed=0, maxJ=7, maxs=3, only=None):
    rnd = random.Random(seed); bad = []
    for _ in range(trials):
        J = ''.join(rnd.choice('01') for _ in range(rnd.randint(0, maxJ)))
        s = only(rnd) if only else ''.join(rnd.choice('01') for _ in range(rnd.randint(0, maxs)))
        got = instance(m, J, s)
        want = zp2_ref.correct(J, s, truth)
        if got != want: bad.append((J, s, got, want))
    return bad
