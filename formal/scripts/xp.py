import sys
import seggen
from seggen import Var, explore

G = seggen.Gen('zlnlLogic', rows='zlnlLogic', logic='LogicLNL', qfiles=['LogicLNL', 'LogicBaseMH'],
               nsmap={'LogicLNL': 'QLNL', 'LogicBaseMH': 'QMH'})
V = lambda n, s='bits': Var(n, 'list', s, hyp='h' + n)

if __name__ == '__main__':
    vs = [V('j'), V('s'), Var('N', 'zeros')]
    print(explore(G, vs, ('EBs', True, 'M j M s M B N', ''), 'SINC'))
    print(explore(G, vs, ('EBs', True, 'M j M s 0 B N', ''), 'JINC'))
    print(explore(G, vs, ('EBs', True, 'M j M s 0 N', ''), 'JINC'))
