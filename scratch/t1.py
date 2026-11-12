import sys
sys.path.insert(0, 'scratch')
from trace import *

q, h, tape, k = sim(m, {}, 0, m.start, set(['TW']))
print(q, h, sorted(tape.items()))
