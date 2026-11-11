"""One-off: copy the machine-independent-in-effect segment lemmas of ZP/Pair.lean into ZP/PairLNLSeg.lean
for `zlnlLogic` (the transitions they use are the same in zp2 and zlnl)."""
import re

pair = open('ZP/Pair.lean').read()

NAMES = ['blkStart', 'copyBody', 'gcBody', 'gcEnd', 'qcBody', 'qcEnd', 'vAcc', 'vRejE', 'vRejC', 'blkVer', 'vUnder',
         'sincE', 'sinc0', 'sinc1', 'jincE', 'jinc0', 'jinc1']


def block(name):
    m = re.search(r'((?:/--[^\n]*-/\n)?theorem %s .*?)\n\n' % name, pair, re.S)
    return m.group(1)


def fix(t):
    return t.replace('zpLogic', 'zlnlLogic').replace('zpBase', 'zlnlLogic')


def vg(t):
    """The end configuration has the dummy cell between `H` and `M_g`."""
    t = t.replace('(hdR Q.GC (1 :: (1 :: (j ++ (1 :: (s ++ [1])))))', '(hdR Q.GC (1 :: (2 :: (1 :: (j ++ (1 :: (s ++ [1]))))))')
    t = t.replace('(ls\' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1])', '(ls\' := [.sym 1, .sym 2, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1])')
    t = t.replace('(k := 39)', '(k := 46)').replace('theorem blkVer ', 'theorem blkVerL ')
    t = t.replace("(ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1])", "(ls' := [.sym 1, .sym 2, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1])")
    t = t.replace('(k := 32)', '(k := 34)').replace('(k := 36)', '(k := 38)')
    return t


head = '''module

public import ZP.LNLRun

@[expose] public section

/-!
# `Z_LNL` pair: segments shared with zp2 (copied from `ZP/Pair.lean` for `zlnlLogic`)

The transitions these segments use are the same in `zp2` and `zlnl` (BLK, the guest-source copy, the
verifier's result dispatch and the successor of `s` / `J`).
-/

namespace ZP.MH

open ZP

def O13 : List Nat := [1, 3]
def T3 : List Nat := [3]
def Z2 : List Nat := [2]

macro "osimp" : tactic =>
  `(tactic| simp [dR, Item.den, List.getD, map_id_app, map_const_len, Fn.app])

'''
out = [head]
for n in NAMES:
    out.append((vg(fix(block(n))) if n in ('vRejE', 'vRejC', 'blkVer') else fix(block(n))) + '\n')
out.append('end ZP.MH\n')
open('ZP/PairLNLSeg.lean', 'w').write('\n'.join(out))
