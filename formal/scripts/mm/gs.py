from mmlib import *
# ---------- setup: the SM loop (w moves one cell toward F, i.e. toward lower indices; `M` is written in front) ----------
# hd form: the head is on the last cell of the left list; F moves it to the previous cell.
V = [('L', 'ALL'), ('R', 'ALL')]
for x in (0, 1):
    spec('smStart%d' % x, 'SM loop entry: write `M`, remember `%d`.' % x, V,
         ('SM', ['L', x + 2], ['R']), ('SM%d' % x, ['L'], [1, 'R']), tt='TT')
    spec('smEnd%d' % x, 'SM loop exit: the blank after `w` receives `%d`.' % x, V,
         ('SM%d' % x, ['L', 0], ['R']), ('RB1', ['L'], [x + 2, 'R']), tt='TT')
    for y in (0, 1):
        spec('smStep%d%d' % (x, y), 'SM loop step.', V,
             ('SM%d' % x, ['L', y + 2], ['R']), ('SM%d' % y, ['L'], [x + 2, 'R']), tt='TT')
print('\n'.join(OUT))
