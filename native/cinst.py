"""Instance checks for the NP = coNP logical machine."""
import random, sys
sys.path.insert(0, '../ref')
import zconp_ref
from zp2_ref import clock

def instance(m, J, s, maxsteps=20_000_000):
    tape = {i: c for i, c in enumerate('M' + J + 'M' + s)}
    h = len(J) + len(s) + 2; q = 'W1'
    for i in range(maxsteps):
        tr = m.d.get((q, tape.get(h, 'B')))
        if tr is None:
            return ('undef', q, tape.get(h, 'B'), i)
        tape[h], mv, q = tr
        h += 1 if mv == 'R' else -1
        if q == 'SINC': return True
        if q == m.beep: return False
    return 'steps'

def check(m, pairs):
    bad = []
    for J, s in pairs:
        got = instance(m, J, s)
        want = zconp_ref.correct(J, s)
        if got != want: bad.append((J, s, got, want))
    return bad

if __name__ == '__main__':
    import zconp
    m = zconp.build()
    print(len(m.states()))
    rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    pairs = [(J, s) for J in ['', '0', '1', '0110100'] for s in ['', '0', '1', '01', '110']]
    pairs += [(''.join(rnd.choice('01') for _ in range(rnd.randint(0, 6))),
               ''.join(rnd.choice('01') for _ in range(rnd.randint(0, 4)))) for _ in range(30)]
    print(check(m, pairs))
