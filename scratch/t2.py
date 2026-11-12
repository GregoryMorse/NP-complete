import sys
sys.path.insert(0, 'scratch')
from trace import *

# run first N steps, print state entrance tapes for a chosen set of "landmark" states
marks = set(sys.argv[2].split(',')) if len(sys.argv) > 2 else set()
N = int(sys.argv[1]) if len(sys.argv) > 1 else 300
out = []


def log(q, h, tape, k):
    if q in marks:
        out.append('%5d %-6s %s' % (k, q, show(tape, h, -8, 40)))


sim(m, {}, 0, m.start, set(), limit=N, log=log)
print('\n'.join(out))
