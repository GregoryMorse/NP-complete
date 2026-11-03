"""Reference semantics for the native P = PP machine (native/zpp.py).

Same guest model, clock and enumeration as zp2_ref; only the language changes:

  L_PP = { s : at least half of the c in {0,1}^(|s|+1) have run(s, c, |s|+1) = ACC }.

L_PP is PP-complete (self-padded majority acceptance; the threshold 'at least
half' is equivalent to 'more than half' for PP).  Hence the machine quasihalts
iff some candidate J decides L_PP within (|s|+2)^(|J|+1) - 1 steps on every s,
iff P = PP.
"""
from itertools import product
from zp2_ref import ACC, run, zp_beeps as _zp_beeps


def in_LPP(s):
    n = len(s)
    acc = sum(run(s, ''.join(c), n + 1) == ACC for c in product('01', repeat=n + 1))
    return 2 * acc >= 2 ** (n + 1)


def zp_beeps(max_beeps=None, max_instances=None):
    return _zp_beeps(truth=in_LPP, max_beeps=max_beeps, max_instances=max_instances)


if __name__ == '__main__':
    import sys
    print(list(zp_beeps(max_beeps=int(sys.argv[1]) if len(sys.argv) > 1 else 10)))
