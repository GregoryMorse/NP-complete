"""Reference semantics for the native NP = coNP machine (native/zconp.py).

Same guest step as zp2_ref, with nondeterminism added at fresh cells:

* Whenever the head moves right onto a never-visited cell (beyond the input
  and everything visited so far) a choice bit is consumed.  Choice 1 puts a
  '1' in the cell; choice 0 leaves it blank.  (The start cell is not a choice.)
* run_nd(P, x, T) is ACC iff some choice sequence makes run(core(P), x, T)
  accept, where core(P) = P with trailing 1s removed.  The machine searches
  the choice sequences depth first (1 before 0), lazily.

  L = { s : run_nd(s, '', |s|+1) = ACC }      (NP-complete, monotone: s in L => s1 in L)

Candidate J (a nondeterministic verifier for the complement) is correct on s
iff run_nd(J, s, T) = ACC  <=>  s not in L,  T = (|s|+2)^(|J|+2) - 1.
The machine beeps at the first s where J is wrong, then moves to J+1.

Why this captures NP = coNP: the prover can only extend the instance by 1s
(a fresh cell holds 1 or blank), and s in L implies s1 in L, so a J that reads
the instance up to the first blank and then checks a certificate for
"not in L" is sound.  Conversely such a J is a polynomial-time NP verifier
for the complement of the NP-complete L.
"""
from zp2_ref import ACC, NAC, rot, succ, clock


def core(P):
    return P.rstrip('1')


def run_choice(P, x, T, D):
    """One deterministic run with choice string D (extended lazily with 1s).
    Returns (result, D_used)."""
    D = list(D)
    k = 0
    R = rot(P[::-1] + '0')[0]
    tape = {i: c for i, c in enumerate(x)}
    h = 0
    top = max(len(x) - 1, 0)
    for _ in range(T + 1):
        a = tape.get(h)
        for _ in range({None: 0, '0': 1, '1': 2}[a]):
            R = rot(R)[0]
        if T == 0:
            return NAC, D[:k]
        T -= 1
        w = R[0]
        d = R[1] if len(R) > 1 else '0'
        t = R[2] if len(R) > 2 else '0'
        if t == '0':
            return (ACC if w == '1' else NAC), D[:k]
        tape[h] = w
        if d == '1':
            h += 1
            if h > top:
                top = h
                if k == len(D):
                    D.append('1')
                if D[k] == '1':
                    tape[h] = '1'
                k += 1
        else:
            h = max(h - 1, 0)
        R, kk = rot(R)
        for _ in range(kk + 1):
            R = rot(R)[0]
    raise AssertionError


def run_nd(P, x, T, stats=None):
    P = core(P)
    D = []
    while True:
        r, used = run_choice(P, x, T, D)
        assert used[:len(D)] == D[:len(used)] and len(used) >= len(D)
        if stats is not None:
            stats['runs'] = stats.get('runs', 0) + 1
            if stats['runs'] > stats.get('cap', 1 << 62):
                raise OverflowError('too many runs')
        if r == ACC:
            return ACC
        D = used
        while D and D[-1] == '0':
            D.pop()
        if not D:
            return NAC
        D[-1] = '0'


def in_L(s):
    return run_nd(s, '', len(s) + 1) == ACC


def correct(J, s, truth=None):
    t = (truth or in_L)(s)
    return (run_nd(J, s, clock(J, s)) == ACC) != t


def zp_beeps(max_beeps=None, max_instances=None, truth=None):
    J, beeps, seen = '', 0, 0
    while True:
        s = ''
        while True:
            if max_instances is not None and seen >= max_instances:
                return
            seen += 1
            if not correct(J, s, truth):
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
