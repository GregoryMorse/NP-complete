from mmlib import *
V = [('Lq','ALL'),('Gz','ALL'),('outr','bits'),('Cb','B0'),('J','bits'),('sv','bits'),('Y2','ALL')]
for o in (2, 3):
    st = ('VW1', ['Lq'], [('c','Gz',0), 0, 0, o, 'outr', 'Cb', 1, 'J', 1, 'sv', 0, 1, 'Y2'])
    en = ('DP3%d' % (o - 2), [1, 'J', 1, 'sv', 1], [1, 'Y2'])
    print(spec('verdictTail%d' % (o-2), 'verdict tail', V, st, en))
