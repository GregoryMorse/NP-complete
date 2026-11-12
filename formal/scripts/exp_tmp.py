import seggen, sys
from seggen import Var, explore
G = seggen.Gen('zlpLogic', rows='zlpLogic', logic='LogicLP', qfiles=['LogicBaseMH', 'LogicLP'],
               nsmap={'LogicBaseMH': 'QMH', 'LogicLP': 'QLP'})
vs = [Var('j', 'list', 'bits'), Var('s', 'list', 'bits'), Var('C', 'list', 'T3'), Var('R', 'list', 'ALL'),
      Var('Z', 'list', 'Z2'), Var('Jx', 'list', 'bits'), Var('X', 'list', 'bits'), Var('Qc', 'list', 'bits'),
      Var('Y', 'list', 'NB'), Var('c', 'list', 'bits'), Var('t', 'list', 'T3'), Var('Fu', 'list', 'ALL'),
      Var('A', 'list', 'ALL')]


def ex(q, d, l, r, stop, **kw):
    print(q, '|', l, '|', r)
    print('   ->', explore(G, vs, (q, d, l, r), stop, **kw))


ex('EAs', False, 'A', '$c R', 'EAs', sub={'c': 2})
ex('EAs', False, 'A', 'B R', 'EX')
ex('EX', False, 'A', '$c R', 'EAs', sub={'c': 2})
ex('EX', False, 'A', '', 'EBs')
ex('EAs', False, 'A', '', 'EBs')
ex('EBs', True, 'A B', 'R', 'EBs')
ex('EBs', True, 'A M', 'R', 'SINC')
ex('EBs', True, 'M Jx M s M 0', 'R', 'JINC')
ex('VA3', False, 'A', '$c R', 'VA3', sub={'c': 2})
ex('VA3', False, 'A', '', 'VA4')
ex('VA3', False, 'A', 'B', 'VA4')
ex('VA3', False, 'A', 'B $c R', 'VA3', sub={'c': 2})
ex('VA4', True, 'A B', 'R', 'VA4')
ex('VA4', True, 'A $c', 'R', 'FB', sub={'c': 3})
ex('FB', False, 'A', '', 'GRB')
ex('BEEP', True, 'M Jx M s M M', 'Y', 'EAs')
