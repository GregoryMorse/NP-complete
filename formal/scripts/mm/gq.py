from mmlib import *
# ---------- Q pass: single-cell moves (hd forms) ----------
V = [('L', 'ALL'), ('R', 'ALL')]


def fmove(name, q, c, w, q2, doc):
    spec(name, doc, V, (q, ['L', c], ['R']), (q2, ['L'], [w, 'R']), tt='TT')


def kmove(name, q, c, w, q2, doc):
    spec(name, doc, V, (q, ['L', c], ['R']), (q2, ['L', w], ['R']), tt='TF')


fmove('q2B', 'Q2', 0, 0, 'Q2', 'Q2 skips a blank.')
kmove('q2Z', 'Q2', 2, 0, 'Q4', 'Q2 blanks an acc 0.')
fmove('q2M', 'Q2', 1, 1, 'N1', 'Q2 meets `Mr`: row loaded.')
for c in (0, 2, 3):
    kmove('q4Step%d' % c, 'Q4', c, c, 'Q4', 'Q4 passes.')
kmove('q4M', 'Q4', 1, 1, 'Q5', 'Q4 meets `Ms`.')
for c in (2, 3):
    kmove('q5Step%d' % c, 'Q5', c, c, 'Q5', 'Q5 passes out cells.')
fmove('q5B', 'Q5', 0, 0, 'Q6', 'Q5 meets a consumed cell.')
fmove('q5M', 'Q5', 1, 1, 'Q6', 'Q5 meets `M_g`.')
fmove('q6M', 'Q6', 1, 1, 'Q80', 'Q6: out used up, load 0.')
fmove('q6y2', 'Q6', 2, 0, 'Q70', 'Q6 takes the out cell 0.')
fmove('q6y3', 'Q6', 3, 0, 'Q71', 'Q6 takes the out cell 1.')
for y, ys in ((0, 2), (1, 3)):
    for c in (2, 3):
        fmove('q7%dStep%d' % (y, c), 'Q7%d' % y, c, c, 'Q7%d' % y, 'Q7 passes out cells.')
        fmove('q8%dStep%d' % (y, c), 'Q8%d' % y, c, c, 'Q8%d' % y, 'Q8 passes acc cells.')
    fmove('q7%dM' % y, 'Q7%d' % y, 1, 1, 'Q8%d' % y, 'Q7 meets `Ms`.')
    fmove('q8%dEnd' % y, 'Q8%d' % y, 0, ys, 'Q2', 'Q8 writes the loaded bit.')
print('\n'.join(OUT))
