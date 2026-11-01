"""Reference semantics for Z_P v2, the natively designed machine (native/).

Guest model (chosen so a 2-symbol host can interpret it with few states):

* A code P is any bit string.  The interpreter works on the cyclic string
  R = reverse(P) + '0' (the appended 0 guarantees R contains a 0), rotated once
  before the first step.
* An *entry* starting at R[0] is parsed cyclically as  w d 1^k 0 ; rot(R)
  rotates R past that entry and returns (rotated R, k).
* Guest tape: one-way infinite, cells B/0/1, input x on cells 0.., head h = 0.
  The guest only ever writes 0/1.  Moving left at cell 0 stays.
* One step: read a = tape[h]; rotate R by iota(a) entries (iota B,0,1 = 0,1,2);
  if the step budget is used up the run ends with NAC (time-out); otherwise
  peek w = R[0], d = R[1], t = R[2] (missing positions read 0).  t = 0: halt,
  ACC iff w = 1.  Else write w, move right iff d = 1, rotate one entry (its
  one-count is k >= 1) and then k + 1 more entries.
* run(P, x, T) is ACC or NAC (a time-out counts as NAC).
* L = { s : some c in {0,1}^(|s|+1) has run(s, c, |s|+1) = ACC }.
* Candidate J is correct on s iff (run(J, s, T) = ACC) == (s in L) with
  T = (|s|+2)^(|J|+2) - 1.  J and s range over strings in shortlex order.
"""
from itertools import product

ACC, NAC = 1, 0


def succ(s):
    """Shortlex successor."""
    if s == '1' * len(s):
        return '0' * (len(s) + 1)
    i = s.rindex('0')
    return s[:i] + '1' + '0' * (len(s) - i - 1)


def rot(R):
    n = len(R)
    j = 2
    while R[j % n] == '1':
        j += 1
    c = (j + 1) % n
    return R[c:] + R[:c], j - 2


def run(P, x, T):
    R = rot(P[::-1] + '0')[0]
    tape = {i: c for i, c in enumerate(x)}
    h = 0
    for _ in range(T + 1):
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
        h = h + 1 if d == '1' else max(h - 1, 0)
        R, k = rot(R)
        for _ in range(k + 1):
            R = rot(R)[0]
    raise AssertionError


def in_L(s):
    n = len(s)
    return any(run(s, ''.join(c), n + 1) == ACC for c in product('01', repeat=n + 1))


def clock(J, s):
    return (len(s) + 2) ** (len(J) + 2) - 1


def correct(J, s, truth=None):
    t = (truth or in_L)(s)
    return (run(J, s, clock(J, s)) == ACC) == t


def zp_beeps(truth=None, max_beeps=None, max_instances=None):
    """Yield (beep index, J, s) for each refutation, in machine order."""
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


def code(entries_list):
    """Code whose cyclic string reverse(P)+'0' is the given (w, d, k) entries."""
    return ''.join(f'{w}{d}' + '1' * k + '0' for w, d, k in entries_list)[:-1][::-1]
