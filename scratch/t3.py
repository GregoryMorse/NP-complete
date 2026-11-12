import sys
sys.path.insert(0, 'scratch')
from trace import *

# print full tape with indices at given step counts
steps = [int(x) for x in sys.argv[1].split(',')]
N = max(steps)


def log(q, h, tape, k):
    if k in steps:
        print(k, q, 'head', h)
        lo, hi = min(tape), max(tape)
        print('  idx ' + ' '.join('%2d' % i for i in range(lo, hi + 1)))
        print('  sym ' + ' '.join(' ' + tape.get(i, 'B') for i in range(lo, hi + 1)))


sim(m, {}, 0, m.start, set(), limit=N, log=log)
