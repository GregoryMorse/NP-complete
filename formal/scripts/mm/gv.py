from mmlib import *
# ---------- group V: the verdict ----------
FRM = ['Y2', 1, 0, 'sv', 1, 'J', 1]            # display, left of Cb
TOP = FRM + ['Cb', 'outr', 1]                  # up to and including Ms
VB = [('Fr', 'NB'), ('Bpr', 'bits'), ('ARr', 'bits'), ('ALr', 'bits'), ('outr', 'bits'), ('Cb', 'B0'),
      ('J', 'bits'), ('sv', 'bits'), ('Y2', 'ALL')]
# e1: J1 / FA at the blank after P (w too short)
for q in ('J1', 'FA'):
  for a in (1, 0):
    spec('vEndShort%s%d' % (q, a), 'The check meets the end of `w` inside `B` (state %s, Mr = %d): outcome 1, up to `VW1`.' % (q, a), VB,
         cfg(q, TOP + ['ALr', 0, 'ARr', a, 'Bpr', 0], 0, []), 'VW1')
# e4: N3 at the blank after the M run (A used up)
VN = [('Mq', 'M1'), ('Bpr', 'bits'), ('ALr', 'bits'), ('outr', 'bits'), ('Cb', 'B0'),
      ('J', 'bits'), ('sv', 'bits'), ('Y2', 'ALL')]
spec('vEndUsed', 'A is used up (state N3): outcome 1, up to `VW1`.', VN,
     cfg('N3', TOP + ['ALr', 0, 1, 'Bpr', 0, 1, 'Mq'], 0, []), 'VW1')
# e5: J1 reads the boundary M: acc != 0, outcome 0
VF = [('Fr', 'NB'), ('Bpr', 'bits'), ('ARr', 'bits'), ('ALr', 'bits'), ('outr', 'bits'), ('Cb', 'B0'),
      ('J', 'bits'), ('sv', 'bits'), ('Y2', 'ALL')]
spec('vEndBad', 'A row differs (J1 reads the boundary): outcome 0, up to `VW1`.', VF,
     cfg('J1', TOP + ['ALr', 0, 'ARr', 1, 'Bpr', 0], 1, ['Fr']), 'VW1')
# e6: setup exits
VS = [('wr', 'bits'), ('on', 'T3'), ('outr', 'bits'), ('Cb', 'B0'), ('J', 'bits'), ('sv', 'bits'), ('Y2', 'ALL')]
spec('vSetupZero', 'm = 0: outcome 1, up to `VW1`.', VS, cfg('X3a', TOP, 2, ['wr']), 'VW1')
spec('vSetupEmpty', 's is empty: outcome 1, up to `VW1`.', VS, cfg('X3a', TOP, 0, []), 'VW1')
spec('vSetupOnes', 's = 1^m: outcome 1, up to `VW1`.', VS, cfg('X3', TOP + ['on'], 0, []), 'VW1')
spec('vSetupNoW', 'w is empty: outcome 1, up to `VW1`.', VS, cfg('SM', TOP + ['on', 0], 0, []), 'VW1')
print('\n'.join(OUT))
