"""Reference semantics for the native linear-time multiplication machine (native/zmul.py).

Guest model: Z_P v2 (zp2_ref) plus a queue of stacks.

* Code, cyclic string R, entries  w d 1^k 0 , one-way guest tape and the
  step loop are those of zp2_ref.  One step: read a = tape[h]; rotate R by
  iota(a); if the step budget is used up the run fails; peek w, d, t.
* t = 1: write w, move (right iff d = 1; left at cell 0 stays), rotate past
  the entry and k + 1 more entries (as in zp2_ref).
* t = 0, d = 0: halt.  w = 1 is a proper halt; w = 0 is a failure.
* t = 0, d = 1: *switch*.  The head cell is erased; the cells h+1, h+2, ..
  (up to the first blank) are taken off the tape and appended, as a stack,
  to the back of a queue that starts with |J| empty stacks; then the stack at
  the front of the queue is taken out and written *reversed* from cell h on
  (its last cell lands on cell h).  Then rotate past the entry (k = 0) and
  1 more entry.  w is not used.
* Output of a proper halt: out = cells 0 .. h-1.

Instance encoding: numbers(u) of zfac_ref (pairs '1b' append a binary digit,
'0' starts the next number); x, y are the first two numbers of s (0 if
missing).  The output must be a pair numeral: out = 1 b_1 1 b_2 .. 1 b_k
(k >= 0), of value z = (b_1 .. b_k)_2.  J is correct on s iff the run halts
properly within T = (|s|+2) * 2^|J| - 1 steps, out is a pair numeral and
z = x * y.  (The machine checks this as: out is a pair numeral, read from its
last cell, and N[0] = N[1] * N[2] for N = numbers(out + '0' + s), which is the
same since out then contributes exactly the number z.)

The machine enumerates J (shortlex) and, for each J, s (shortlex), and beeps
at the first s on which J is wrong.  It quasihalts iff some J is correct on
every s, iff multitape Turing machines multiply in linear time:
* a k-tape machine is simulated with O(1) overhead per step and O(|J|)
  switches per access: every stack carries tags at both ends, so after a
  switch the head shows which stack came in and which end is up (a stack is
  reversed each time it comes in, so within two passes of the queue every
  stack comes in either way up);
* conversely the model is a constant number of stacks, each accessed at both
  ends (a deque), plus one tape; deques cost amortized O(1) on two stacks.
"""
from zp2_ref import succ, rot
from zfac_ref import numbers

IOTA = {None: 0, '0': 1, '1': 2}


def run(P, x, T, r):
    """out (a string) if the run halts properly within T steps, else None."""
    R = rot(P[::-1] + '0')[0]
    tape = {i: c for i, c in enumerate(x)}
    h = 0
    queue = [[] for _ in range(r)]
    while True:
        for _ in range(IOTA[tape.get(h)]):
            R = rot(R)[0]
        if T == 0:
            return None
        T -= 1
        w = R[0]
        d = R[1] if len(R) > 1 else '0'
        t = R[2] if len(R) > 2 else '0'
        if t == '0' and d == '0':
            return ''.join(tape[i] for i in range(h)) if w == '1' else None
        if t == '0':
            st, i = [], h + 1
            while i in tape:
                st.append(tape.pop(i))
                i += 1
            tape.pop(h, None)
            queue.append(st)
            for i, c in enumerate(reversed(queue.pop(0))):
                tape[h + i] = c
            k = 0
        else:
            tape[h] = w
            h = h + 1 if d == '1' else max(h - 1, 0)
        R, k = rot(R)
        for _ in range(k + 1):
            R = rot(R)[0]


def clock(J, s):
    return (len(s) + 2) * 2 ** len(J) - 1


def pair_value(out):
    """z if out = 1 b_1 .. 1 b_k is a pair numeral, else None."""
    if len(out) % 2 or any(c != '1' for c in out[::2]):
        return None
    return int('0' + out[1::2], 2)


def check(out, s):
    N = numbers(s) + [0, 0]
    return pair_value(out) == N[0] * N[1]


def correct(J, s):
    out = run(J, s, clock(J, s), len(J))
    return out is not None and check(out, s)


def zp_beeps(max_beeps=None, max_instances=None):
    """Yield (beep index, J, s) for each refutation, in machine order."""
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
