from mmlib import *
# ---------- N phase (more rows?) and the RB shift from N5 ----------
V = [('L', 'ALL'), ('R', 'ALL')]


def fmove(name, q, c, w, q2, doc):
    spec(name, doc, V, (q, ['L', c], ['R']), (q2, ['L'], [w, 'R']), tt='TT')


def kmove(name, q, c, w, q2, doc):
    spec(name, doc, V, (q, ['L', c], ['R']), (q2, ['L', w], ['R']), tt='TF')


for c in (2, 3):
    fmove('n1Step%d' % c, 'N1', c, c, 'N1', 'N1 passes B.')
fmove('n1End', 'N1', 0, 0, 'N2', 'N1 meets `P`.')
fmove('n2M', 'N2', 1, 1, 'N3', 'N2 reads the boundary.')
fmove('n3M', 'N3', 1, 1, 'N3', 'N3 passes a consumed A entry.')
for c in (2, 3):
    kmove('n3Bit%d' % c, 'N3', c, c, 'N5', 'N3 reads a next A entry: more rows.')
kmove('n3B', 'N3', 0, 0, 'VC1', 'N3: A used up.')
kmove('n5M', 'N5', 1, 1, 'N5', 'N5 returns over consumed entries.')
kmove('n5End', 'N5', 0, 0, 'RB2', 'N5 meets `P`.')
for x in (0, 1):
    spec('rb2Step%d' % x, 'RB2 reads a B bit: it moves into the hole.', V,
         ('RB2', ['L', 0], [x + 2, 'R']), ('RB1', ['L', x + 2], [0, 'R']), tt='FF')
spec('rbEnd2', 'RB1 meets `Mr` right after the bits: rewind (RS1).', V,
     ('RB1', ['L', 0], [1, 'R']), ('RS1', ['L', 0, 1], ['R']), tt='TF')
print('\n'.join(OUT))
