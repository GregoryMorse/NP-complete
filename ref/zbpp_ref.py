"""Reference semantics for the native promise-BPP machine (native/zbpp.py).

Same guest model, clock and enumeration as zp2_ref.  For s with n = |s| and
N = 2^(n+1) certificates c in {0,1}^(n+1), let acc be the number with
run(s, c, n+1) = ACC and rej = N - acc.  The promise problem CAPP_s is

  YES  if 4 acc >= 3 N,
  NO   if 4 rej >= 3 N,
  (neither: s is outside the promise).

This is the circuit acceptance probability problem with gap 3/4 vs 1/4 in the
self-padded form of zpp_ref: it is complete for promise-BPP under the padding
reduction (amplify the BPP machine to error 1/4 first; unread certificate bits
do not change the counts' ratio).  Candidate J is correct on s iff s is outside
the promise or (run(J, s, T) = ACC) == (s is YES).  The machine beeps at the
first s on which J is wrong, so it quasihalts iff some J decides CAPP on the
promise within T = (|s|+2)^(|J|+1) - 1 steps, iff promise-P = promise-BPP.
"""
from itertools import product
from zp2_ref import ACC, run, clock, succ


def capp(s):
    """True (YES), False (NO) or None (outside the promise)."""
    n = len(s)
    N = 2 ** (n + 1)
    acc = sum(run(s, ''.join(c), n + 1) == ACC for c in product('01', repeat=n + 1))
    if 4 * acc >= 3 * N:
        return True
    if 4 * (N - acc) >= 3 * N:
        return False
    return None


def correct(J, s):
    t = capp(s)
    return t is None or (run(J, s, clock(J, s)) == ACC) == t


def zp_beeps(max_beeps=None, max_instances=None):
    J, beeps, seen = '', 0, 0
    while True:
        s = ''
        while True:
            if max_instances is not None and seen >= max_instances:
                return
            seen += 1
            if not correct(J, s):
                yield beeps, J, s
                beeps += 1
                if max_beeps is not None and beeps >= max_beeps:
                    return
                break
            s = succ(s)
        J = succ(J)


if __name__ == '__main__':
    import sys
    print(list(zp_beeps(max_beeps=int(sys.argv[1]) if len(sys.argv) > 1 else 10)))
