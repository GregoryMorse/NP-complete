from mmlib import *
# ---------- row end: D0, D1, D3 (acc = 0 check) and the failing mark (Z1) ----------
V = [('L', 'ALL'), ('R', 'ALL')]


def fmove(name, q, c, w, q2, doc):
    spec(name, doc, V, (q, ['L', c], ['R']), (q2, ['L'], [w, 'R']), tt='TT')


def kmove(name, q, c, w, q2, doc):
    spec(name, doc, V, (q, ['L', c], ['R']), (q2, ['L', w], ['R']), tt='TF')


kmove('d0P', 'D0', 0, 0, 'D1', 'D0 on `P`.')
for c in (2, 3):
    kmove('d1Step%d' % c, 'D1', c, c, 'D1', 'D1 passes a bit of B.')
kmove('d1End', 'D1', 1, 1, 'D3', 'D1 meets `Mr = M`.')
kmove('d3Zero', 'D3', 2, 2, 'D3', 'D3 reads an acc 0.')
fmove('d3End', 'D3', 0, 0, 'Q2', 'D3 reaches the hole: acc = 0.')
fmove('d3One', 'D3', 3, 2, 'Z1', 'D3 reads an acc 1: mark it 0.')
for c in (2, 3):
    fmove('z1Step%d' % c, 'Z1', c, c, 'Z1', 'Z1 passes an acc cell.')
fmove('z1End', 'Z1', 1, 1, 'G2', 'Z1 meets `Mr`.')
print('\n'.join(OUT))
