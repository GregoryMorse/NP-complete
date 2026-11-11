from mmlib import *
# ---------- group J: the j-step, rewind, fetch ----------
def jc(sub):
    a, v, x = sub['a'], sub['v'], sub['x']
    return 5 - x if (a == 0 and v == 3) else x

def cfgT(q, dl, dr):
    """hd form: dr = display-right items, whose display-first cell is the head."""
    return (q, rev(dr), rev(dl))

JV = [('Tl', 'ALL'), ('ALr', 'bits'), ('ARr1', 'bits'), ('Bpr', 'bits'), ('Fr', 'ALL')]
JF = ('f', 'jc a v x', jc)
spec('jMore', 'One j-step, more cells follow: `v` slides into `P`, `acc[j]` is updated, the hole moves on; the head ends on the next cell.',
     JV, cfg('J1', ['Tl', 1, 'ALr', 0, '@x', '@y', 'ARr1', '@a', 'Bpr', 0], '@v', ['Fr']),
     cfgT('J1', ['Tl', 1, 'ALr', JF, 0, '@y', 'ARr1', '@a', 'Bpr', '@v', 0], ['Fr']),
     params=[('a', 'bm'), ('v', 'bits'), ('x', 'bits'), ('y', 'bits')], tt='FT')
JV2 = [('Tl', 'ALL'), ('ALr', 'bits'), ('Bpr', 'bits'), ('Fr', 'ALL')]
spec('jLast', 'The last j-step of a B row: `Mr := M`, the hole is at the right end of the accumulator.',
     JV2, cfg('J1', ['Tl', 1, 'ALr', 0, '@x', '@a', 'Bpr', 0], '@v', ['Fr']),
     cfg('RS1', ['Tl', 1, 'ALr', JF], 0, [1, 'Bpr', '@v', 0, 'Fr']),
     params=[('a', 'bm'), ('v', 'bits'), ('x', 'bits')])
# rewind: one swap, and the end
RV = [('Lq', 'ALL'), ('R', 'ALL')]
spec('rsStep', 'Rewind: the hole swaps with its neighbour.', RV,
     ('RS1', ['Lq'], [0, '@x', 'R']), ('RS1', ['Lq', '@x'], [0, 'R']), params=[('x', 'bits')])
spec('rsEnd', 'Rewind exit: the head meets `Ms` and returns to the hole (state `G1`).', RV,
     ('RS1', ['Lq'], [0, 1, 'R']), ('G1', ['Lq', 0], [1, 'R']), tt='FT')
print('@[simp] def jc (a v x : Nat) : Nat := if a = 0 ∧ v = 3 then 5 - x else x\n')
print('\n'.join(OUT))
