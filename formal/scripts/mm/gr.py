from mmlib import *
# ---------- RB loop: the hole slides toward higher indices through the bits of B ----------
V = [('L', 'ALL'), ('R', 'ALL')]
for x in (0, 1):
    spec('rbStep%d' % x, 'RB loop step: bit `%d` moves into the hole.' % x, V,
         ('RB1', ['L', 0], [x + 2, 'R']), ('RB1', ['L', x + 2], [0, 'R']), tt='TF')
spec('rbEnd', 'RB loop exit: `M` is written into the hole, the head runs on to `RS1`.', V,
     ('RB1', ['L', 0], [0, 1, 'R']), 'RS1', tt='TF')
print('\n'.join(OUT))
