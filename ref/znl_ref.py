"""Reference semantics for the native L = NL machine (native/zlnl.py).

Truth (one-way verifier).  run1(P, c, T) is zp2_ref.run with a one-way head:
the step 'move left' (d = 0) leaves the head where it is.  For s with
n = |s|,

    L_NL = { s : some c in {0,1}^(n+1) has run1(s, c, n+1) = ACC }.

L_NL is in NL: guess c cell by cell as the head reaches it, keeping the
rotation state of R (an index into s), the head position, the current cell
and a step counter, all in O(log n) bits.  It is NL-hard under log-space
reductions: for a log-space NTM N and an input x, the configuration graph of
N on x has polynomially many nodes; a program text of polynomial size can
hard-wire it (one block of entries per configuration, the certificate bit
under the head choosing the successor, the head moving right after each
read), and padding makes |s|+1 exceed both the number of steps and the
number of certificate cells used.  So L_NL is NL-complete.

Decider: the multihead read-only model of zmh_ref.  Candidate J is correct on
s iff (run_mh(J, s, T) = ACC) == (s in L_NL), T = (|s|+2)^(|J|+1) - 1.  A
log-space machine is a multihead two-way DFA running in polynomial time, so
the machine quasihalts iff some J decides L_NL within the clock, iff L_NL is
in L, iff L = NL.
"""
from itertools import product
from zp2_ref import ACC, NAC, rot, succ, clock
from zmh_ref import run_mh


def run1(P, x, T):
    R = rot(P[::-1] + '0')[0]
    tape = {i: c for i, c in enumerate(x)}
    h = 0
    while True:
        a = tape.get(h)
        for _ in range({None: 0, '0': 1, '1': 2}[a]):
            R = rot(R)[0]
        if T == 0:
            return NAC
        T -= 1
        w = R[0]
        d = R[1] if len(R) > 1 else '0'
        t = R[2] if len(R) > 2 else '0'
        if t == '0':
            return ACC if w == '1' else NAC
        tape[h] = w
        if d == '1':
            h += 1
        R, k = rot(R)
        for _ in range(k + 1):
            R = rot(R)[0]


def in_LNL(s):
    n = len(s)
    return any(run1(s, ''.join(c), n + 1) == ACC for c in product('01', repeat=n + 1))


def correct(J, s):
    return (run_mh(J, s, clock(J, s)) == ACC) == in_LNL(s)


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
