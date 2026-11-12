from mmlib import *
# ---------- verdict stage 2: from VW1 (outcome o) to the dispatch DP3o ----------
V = [('Lq', 'ALL'), ('Gz', 'ALL'), ('outr', 'bits'), ('Cb', 'B0'), ('J', 'bits'), ('sv', 'bits'), ('Y2', 'ALL')]
for o in (2, 3):
    st = ('VW1', ['Lq'], [('c', 'Gz', 0), 0, 0, o, 'outr', 'Cb', 1, 'J', 1, 'sv', 0, 1, 'Y2'])
    en = ('DP3%d' % (o - 2), [1, 'J', 1, 'sv', 1], [1, 'Y2'])
    spec('verdictTail%d' % (o - 2), 'Verdict stage 2 (outcome %d): erase the stretches and dispatch.' % (o - 2), V, st, 'DP3%d' % (o - 2))
print('\n'.join(OUT))
