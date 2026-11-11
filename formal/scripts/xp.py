import sys
import seggen
from seggen import Var, explore

G = seggen.Gen('zlnlLogic', rows='zlnlLogic', logic='LogicLNL', qfiles=['LogicLNL', 'LogicBaseMH'],
               nsmap={'LogicLNL': 'QLNL', 'LogicBaseMH': 'QMH'})

V = lambda n, s='bits': Var(n, 'list', s, hyp='h' + n)

if __name__ == '__main__':
    vs = [V('Jl'), V('Jr'), V('s'), V('s1'), V('s2'), V('Y', 'NB'), V('Z0', 'NB'), V('ud'), V('Z', 'ALL')]
    print(explore(G, vs, ('UCP', False, 'Jl M Jr M s1', '$b s2 M Y B Z0 M M ud'), 'UCP', sub={'b': 3}))
    print(explore(G, vs, ('UCP', False, 'Jl M Jr M s', 'M Y B Z0 M M ud'), 'UDW'))
    print(explore(G, vs, ('UDW', False, '', 'Jl $b M Jr M s M Y B Z'), 'U0', sub={'b': 3}))
    print(explore(G, vs, ('UDW', False, '', 'M Jr M s M Y B Z'), 'QC'))
    print(explore(G, vs, ('U0', False, 'Jl M', 'Jr M s M Y B'), 'UCP'))
