from mmlib import *
# ---------- fetch: single-cell moves (hd forms).  F: toward lower indices, K: toward higher ----------
V = [('L', 'ALL'), ('R', 'ALL')]


def fmove(name, q, c, w, q2, doc):
    """read c in state q (head = last of L), write w, move F."""
    spec(name, doc, V, (q, ['L', c], ['R']), (q2, ['L'], [w, 'R']), tt='TT')


def kmove(name, q, c, w, q2, doc):
    """read c, write w, move K: the head lands on R[0]."""
    spec(name, doc, V, (q, ['L', c], ['R']), (q2, ['L', w], ['R']), tt='TF')


for x in (0, 2, 3):
    fmove('g1Step%d' % x, 'G1', x, x, 'G1', 'G1 passes a blank or bit.')
fmove('g1End', 'G1', 1, 1, 'GA', 'G1 meets `Mr`.')
for x in (2, 3):
    fmove('gaStep%d' % x, 'GA', x, x, 'GA', 'GA passes a bit.')
    fmove('g2Step%d' % x, 'G2', x, x, 'G2', 'G2 passes a bit.')
    fmove('faBit%d' % x, 'FA', x, x, 'FB', 'FA reads a bit.')
    fmove('fbStep%d' % x, 'FB', x, x, 'FB', 'FB passes a bit.')
fmove('gaEnd', 'GA', 0, 0, 'FA', 'GA meets the hole `P`.')
fmove('g2End', 'G2', 0, 0, 'J1', 'G2 meets `P`: next j-step.')
kmove('faM', 'FA', 1, 1, 'D0', 'FA meets the boundary: dry/done.')
kmove('faB', 'FA', 0, 0, 'VC1', 'FA meets a blank: `w` ends: verdict 1.')
fmove('fbM', 'FB', 1, 1, 'FC', 'FB meets the boundary.')
kmove('fbB', 'FB', 0, 0, 'D0', 'FB meets a blank: no boundary yet: dry row.')
fmove('fcM', 'FC', 1, 1, 'FC', 'FC passes a consumed `A` entry.')
kmove('fcB', 'FC', 0, 0, 'FD0', 'FC meets the end of A: a = 0.')
kmove('fcZ', 'FC', 2, 1, 'FD0', 'FC reads an A entry 0: consume it.')
kmove('fcO', 'FC', 3, 1, 'FD1', 'FC reads an A entry 1: consume it.')
for d, fd in ((0, 'FD0'), (1, 'FD1')):
    for c in (1, 2, 3):
        kmove('fd%dStep%d' % (d, c), fd, c, c, fd, 'FD passes a cell.')
    kmove('fd%dEnd' % d, fd, 0, 0, 'FE%d' % d, 'FD meets `P`.')
    for c in (2, 3):
        kmove('fe%dStep%d' % (d, c), 'FE%d' % d, c, c, 'FE%d' % d, 'FE passes a bit.')
    for c in (1, 0):
        fmove('fe%dEnd%d' % (d, c), 'FE%d' % d, c, 1 if d == 0 else 0, 'G2', 'FE writes `Mr := a`.')
print('\n'.join(OUT))
