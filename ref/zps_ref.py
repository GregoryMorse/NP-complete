"""Reference semantics for the native P = PSPACE machine (native/zps.py).

Same guest model, clock and enumeration as zp2_ref; the language is a
quantified one.  For s with n = |s| and certificates c = c_0 .. c_n:

  G(s) = Q_0 c_0 Q_1 c_1 ... Q_n c_n : run(s, c, n+1) = ACC

where Q_n = EXISTS and the quantifiers alternate going left (Q_i = EXISTS iff
n - i is even).  L_PS = { s : G(s) }.  This is QBF with a linear-time matrix,
PSPACE-complete by the padding argument (dummy certificate bits fix the
quantifier pattern; unread bits do not change the value).

The machine evaluates the game tree depth-first with short-circuiting, the
first child of every node being c_i = 1.
"""
from zp2_ref import ACC, run, zp_beeps as _zp_beeps


def in_LPS(s):
    n = len(s)

    def val(prefix):
        i = len(prefix)
        if i == n + 1:
            return run(s, prefix, n + 1) == ACC
        exists = (n - i) % 2 == 0
        a = val(prefix + '1')
        if a == exists:            # short circuit (same value either way)
            return a
        return val(prefix + '0')
    return val('')


def zp_beeps(max_beeps=None, max_instances=None):
    return _zp_beeps(truth=in_LPS, max_beeps=max_beeps, max_instances=max_instances)


if __name__ == '__main__':
    import sys
    print(list(zp_beeps(max_beeps=int(sys.argv[1]) if len(sys.argv) > 1 else 10)))
