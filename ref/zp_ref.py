"""Reference implementation of the abstract program Z_P (brief §3.3).

Every encoding convention used by the compiled machine is fixed here; the
counter-machine program (compiler/zp_cm.py) and the Turing machine compiled
from it are tested against this file.  See docs/spec.md for the prose spec.

Conventions (summary; spec.md is authoritative)
-----------------------------------------------
* A bitstring s = b1..bm is represented by the natural  rep(s) = int('1'+s, 2)
  (shortlex rank + 1).  rep(eps) = 1.  |s| = len(N) = N.bit_length() - 1.
* Program decoding (total).  The code s is read *right to left*: popping the
  least significant bit of rep(s).  Reading past the end (rep == 1) is a
  decoding failure, which makes the guest REJECT.
  The code is a list of entries, each a unary number  1^e 0.  The machine
  state is an *offset* o (start o = 0); scanning symbol a it uses entry
  number o + a.  Entry value e = 4k + 2d + w:  w = symbol to write,
  d = 1 for right / 0 for left, k = 0 means HALT with output ACCEPT iff
  w = 1, k >= 1 means the new offset is k - 1.  (A TM with states
  0..m-1 is coded by putting state i at offset 2i.)
* Guest: 1-tape 2-symbol TM, blank 0, two-way infinite tape.
* Input (self-delimiting): c = b1..bm is written as 1 b1 1 b2 ... 1 bm
  starting at the head cell, rest blank.
* One guest step = one transition, halting transitions included.
  run(P, X, t) performs at most t steps.
* L = { s : exists c with rep(c) <= rep(s) such that
            prog(s) on input c ACCEPTs within |s| steps }.
* Clock for candidate J on instance S:  T(J,S) = (|s|+2) ** |code(J)|.
* Z_P: J = 1, 2, ... (rep of the candidate code); S = 1, 2, ...; candidate J
  is refuted at S iff run(J, S, T(J,S)) != [S in L]  (TIMEOUT never equals).
  On refutation: BEEP, J += 1, S := 1.
"""

ACC, REJ, TIMEOUT = 1, 0, 2


def length(N):
    """|s| for N = rep(s)."""
    return N.bit_length() - 1


def rep(s):
    return int('1' + s, 2)


def unrep(N):
    return bin(N)[3:]


def encode_input(X):
    """Right stack (LSB = head cell) for input with rep X."""
    R = 0
    while X > 1:
        b = X & 1
        X >>= 1
        R = 2 * R + b
        R = 2 * R + 1
    return R


class _Fail(Exception):
    pass


def lookup(P, idx):
    """Return (w, d, k) of entry number idx of code P, or None if the code
    ends first."""
    pc = P
    e = 0
    while True:
        if pc == 1:
            return None
        b = pc & 1
        pc >>= 1
        if b:
            if idx == 0:
                e += 1
        elif idx == 0:
            return e & 1, (e >> 1) & 1, e >> 2
        else:
            idx -= 1


def run(P, X, t, trace=None):
    """Simulate prog(P) on input X for at most t steps."""
    R = encode_input(X)
    Lt = 0
    q = 0
    for _ in range(t):
        a = R & 1
        R1 = R >> 1
        e = lookup(P, q + a)
        if e is None:
            return REJ
        w, d, k = e
        if k == 0:
            return ACC if w else REJ
        q = k - 1
        if d:
            Lt = 2 * Lt + w
            R = R1
        else:
            R = 2 * (2 * R1 + w) + (Lt & 1)
            Lt >>= 1
    return TIMEOUT


def in_L(S):
    n = length(S)
    return any(run(S, C, n) == ACC for C in range(1, S + 1))


def clock(J, S):
    return (length(S) + 2) ** length(J)


def zp_beeps(truth=None, candidates=None, clock_fn=clock, max_beeps=None,
             max_instances=None):
    """Yield (beep_index, J, S) for each beep of Z_P.

    truth(S) -> bool replaces membership in L (P-language swap test).
    candidates: iterable of J values replacing J = 1, 2, 3, ... (controlled
    enumeration test).  If the iterable is exhausted the generator stops.
    max_instances bounds the total number of instances examined.
    """
    truth = truth or in_L
    cands = iter(candidates) if candidates is not None else _naturals(1)
    beeps = 0
    examined = 0
    for J in cands:
        S = 1
        while True:
            if max_instances is not None and examined >= max_instances:
                return
            examined += 1
            want = ACC if truth(S) else REJ
            r = run(J, S, clock_fn(J, S))
            if r != want:
                yield beeps, J, S
                beeps += 1
                if max_beeps is not None and beeps >= max_beeps:
                    return
                break
            S += 1


def _naturals(k):
    while True:
        yield k
        k += 1


# ---------------------------------------------------------------- helpers
def assemble(entries):
    """Build rep(code) from a list of (w, d, k) entries, in reading order.
    Entry 2i+a is the transition of state i on symbol a when next-states
    are written as k = 2*state + 1 (use tm_code() for that)."""
    bits = []                       # reading order (LSB first)
    for w, d, k in entries:
        bits += [1] * (4 * k + 2 * d + w) + [0]
    N = 1
    for b in reversed(bits):        # first-read bit must be the LSB
        N = 2 * N + b
    return N


def tm_code(delta):
    """delta: list over states i of (tr_on_0, tr_on_1); tr = ('H', out) or
    (w, d, next_state).  Returns rep(code) with state i at offset 2i."""
    ents = []
    for tr0, tr1 in delta:
        for tr in (tr0, tr1):
            if tr[0] == 'H':
                ents.append((tr[1], 0, 0))
            else:
                w, d, nxt = tr
                ents.append((w, d, 2 * nxt + 1))
    return assemble(ents)


if __name__ == '__main__':
    for i, J, S in zp_beeps(max_beeps=12):
        print(i, J, repr(unrep(J)), S, repr(unrep(S)))
