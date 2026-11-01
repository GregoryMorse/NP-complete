"""Transition coverage of the logical machine from random instances
(tape  M J M s M, state GRB), run until the instance ends (next GRB after
s++/J++ is reached via SINC/JINC)."""
import random, sys
import zp2

def cover(trials=200, seed=1, maxsteps=3_000_000):
    m = zp2.build()
    rnd = random.Random(seed)
    used = set()
    for _ in range(trials):
        J = ''.join(rnd.choice('01') for _ in range(rnd.randint(0, 9)))
        s = ''.join(rnd.choice('01') for _ in range(rnd.randint(0, 4)))
        tape = {}
        cells = 'M' + J + 'M' + s
        for i, c in enumerate(cells):
            tape[i] = c
        h = len(cells); q = 'GRB'
        seen_inst = 0
        for step in range(maxsteps):
            a = tape.get(h, 'B')
            used.add((q, a))
            w, mv, q = m.d[(q, a)]
            tape[h] = w; h += 1 if mv == 'R' else -1
            if q in ('SINC', 'JINC'):
                seen_inst += 1
                if seen_inst >= 2:
                    break
    return m, used

if __name__ == '__main__':
    m, used = cover(int(sys.argv[1]) if len(sys.argv) > 1 else 100)
    un = sorted(set(m.d) - used)
    print(len(m.d), len(used), len(un))
    print(un)
