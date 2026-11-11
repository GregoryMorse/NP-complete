"""Reference semantics for the native NP-in-P/poly machine (native/zppoly.py).

Same guest model as zp2_ref and the same NP-complete language L.  Here a
*degree* K (any bit string; only |K| matters) fixes the budget

    T(K, n) = (n+2)^(|K|+1) - 1,

and for each input length n the machine searches for an *advice program* a: a
guest code of any length that decides L on every s in {0,1}^n.  A run of a is
charged |a| steps up front:

    prun(a, s, T) = run(a, s, T - |a|) if |a| <= T, else time-out.

K is good on n iff some a with |a| <= T(K, n) has (prun(a, s, T) = ACC) ==
(s in L) for every s in {0,1}^n.  Programs longer than T(K, n) always time
out, so the search over a stops at the first a with |a| > T(K, n).

The machine enumerates K in shortlex order.  For each K it runs through
n = 0, 1, 2, ..., for each n through a = '', '0', '1', '00', ... (shortlex)
and for each a through s in {0,1}^n (binary order).  A wrong s moves to the
next a; a correct last s moves to n + 1 with a = ''.  It beeps when a reaches
length T(K, n) + 1, and moves to the next K with n = 0.

So it quasihalts iff some K is good on every n, iff L has polynomial-size
programs that run in polynomial time, iff L in P/poly, iff NP is in P/poly
(L is NP-complete under polynomial-time reductions, which preserve P/poly).
"""
from zp2_ref import ACC, run, in_L, succ


def T(K, n):
    return (n + 2) ** (len(K) + 1) - 1


def prun(a, s, t):
    return run(a, s, t - len(a)) if len(a) <= t else 0


def binsucc(s):
    """Binary successor of a fixed-length string, None on overflow."""
    if '0' not in s:
        return None
    i = s.rindex('0')
    return s[:i] + '1' + '0' * (len(s) - i - 1)


def events(truth=None, max_events=None):
    """Yield ('beep', K, n) at every refutation of a degree K and
    ('ok', K, n, a) when K passes length n with advice a."""
    truth = truth or in_L
    K, cnt = '', 0
    while True:
        n = 0
        while True:
            a = ''
            while True:
                t = T(K, n)
                if len(a) > t:
                    ev = ('beep', K, n)
                    break
                s = '0' * n
                while s is not None and (prun(a, s, t) == ACC) == truth(s):
                    s = binsucc(s)
                if s is None:
                    ev = ('ok', K, n, a)
                    break
                a = succ(a)
            yield ev
            cnt += 1
            if max_events is not None and cnt >= max_events:
                return
            if ev[0] == 'beep':
                break
            n += 1
        K = succ(K)


def zp_beeps(truth=None, max_beeps=None):
    """(beep index, K, n) at each refutation."""
    b = 0
    for ev in events(truth):
        if ev[0] == 'beep':
            yield b, ev[1], ev[2]
            b += 1
            if max_beeps is not None and b >= max_beeps:
                return


if __name__ == '__main__':
    import sys
    for ev in events(max_events=int(sys.argv[1]) if len(sys.argv) > 1 else 10):
        print(ev)
