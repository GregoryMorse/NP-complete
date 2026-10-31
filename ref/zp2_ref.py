"""Reference for Z_P v2, the native (directly designed) machine. Spec: docs/native.md.

Differences from zp_ref.py (v1), chosen so that every operation is cheap for a
TM that keeps all data as bit fields on its tape:

* Guest: one-way infinite tape (moving left at cell 0 stays), symbols {B, 0, 1},
  input x on cells 0..|x|-1, head on cell 0.  The guest only writes 0 or 1.
* Code P: if P is empty or starts with '1' it has no entries.  Otherwise
  P[1:] is read left to right as entries  w d 1^k 0  (w, d bits; k >= 0).  An
  incomplete tail is ignored.  E_0 .. E_{m-1} are the entries.
* Step from offset o, reading a: i = o + iota(a) with iota(B, 0, 1) = 0, 1, 2.
  If i >= m: REJ.  E_i = (w, d, k): k = 0 halts with ACC iff w = 1.  Otherwise
  write w, move right if d = 1 (else left), o := k - 1, and REJ at once if o > m.
* run(P, x, T): at most T steps, then TIMEOUT.
* L = { s : some c in {0,1}^(|s|+1) makes run(s, c, |s|+1) = ACC }.
* Clock T(J, s) = (|s|+2)^(|J|+1) - 1.
* Candidates J and instances s are strings in shortlex order from the empty string.
"""
from itertools import product

ACC, REJ, TIMEOUT = 1, 0, 2


def succ(s):
    """Shortlex successor."""
    if s == '1' * len(s):
        return '0' * (len(s) + 1)
    i = s.rindex('0')
    return s[:i] + '1' + '0' * (len(s) - i - 1)


def entries(P):
    if not P or P[0] == '1':
        return []
    out, i, b = [], 1, P
    while i + 2 <= len(b):
        w, d = int(b[i]), int(b[i + 1])
        j = i + 2
        while j < len(b) and b[j] == '1':
            j += 1
        if j >= len(b):
            break
        out.append((w, d, j - i - 2))
        i = j + 1
    return out


def run(P, x, T, E=None):
    E = entries(P) if E is None else E
    m = len(E)
    tape = {i: int(c) for i, c in enumerate(x)}
    h = o = 0
    for _ in range(T):
        a = tape.get(h)
        i = o + (0 if a is None else a + 1)
        if i >= m:
            return REJ
        w, d, k = E[i]
        if k == 0:
            return ACC if w else REJ
        tape[h] = w
        h = h + 1 if d else max(h - 1, 0)
        o = k - 1
        if o > m:
            return REJ
    return TIMEOUT


def in_L(s):
    n = len(s)
    E = entries(s)
    return any(run(s, ''.join(c), n + 1, E) == ACC for c in product('01', repeat=n + 1))


def clock(J, s):
    return (len(s) + 2) ** (len(J) + 1) - 1


def zp_beeps(truth=None, max_beeps=None, max_instances=None, candidates=None):
    truth = truth or in_L
    beeps = examined = 0
    J = ''
    ci = 0
    while True:
        if candidates is not None:
            if ci >= len(candidates):
                return
            J = candidates[ci]
        s = ''
        while True:
            if max_instances is not None and examined >= max_instances:
                return
            examined += 1
            want = ACC if truth(s) else REJ
            if run(J, s, clock(J, s)) != want:
                yield beeps, J, s
                beeps += 1
                if max_beeps is not None and beeps >= max_beeps:
                    return
                break
            s = succ(s)
        if candidates is None:
            J = succ(J)
        ci += 1


def code(entries_list):
    """Assemble a code from (w, d, k) entries."""
    return '0' + ''.join(f'{w}{d}' + '1' * k + '0' for w, d, k in entries_list)
