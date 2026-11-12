import seggen
from seggen import Var
g = seggen.Gen('mhBase', rows='mhBase', logic='LogicBaseMH', qfiles=['LogicBaseMH'], nsmap={'LogicBaseMH': 'QMH'})
vars_ = [Var('Qw', 'list', 'bits', hyp='hQ'), Var('g', 'zeros'), Var('W', 'list', 'NB', hyp='hW')]
print(g.theorem('segA0', 'Count-down step with an empty right-of-head word.',
    '(Qw W : List Nat) (g ch : Nat) (hch : ch ∈ bits) (hQ : Bits Qw) (hW : NoB W)', vars_,
    ('BK2', True, 'Qw g B $ch', 'M W'), ('TW', True, 'Qw', 'g B $cd M W'),
    cases=[('ch', [2, 3], 'hch')], derived={'cd': ('(cdn ch)', lambda s: 0 if s['ch'] == 2 else 2)}))
