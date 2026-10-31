"""Integer multiplication in linear time on multitape TMs (docs/spec.md §2.3).

Guest: a k-tape, 2-symbol TM (k >= 1 read from the code).  The code is a list of
unary entries as in zp_ref.py.  Entry 0 has value k - 1.  With offset o and the
symbols under the heads a_1..a_k (sym = a_1 a_2 .. a_k in binary, tape 1 most
significant), the machine uses entry 1 + o + sym, value e = 4^k * kn + act, where
act = sum_i (w_i + 2 d_i) 4^(k-i): write w_i on tape i, move it right if d_i = 1,
else left.  kn = 0 halts (no action), otherwise the new offset is kn - 1.
Input: tape 1 holds enc(s) from its head (zp_ref.encode_input); others blank.
Output: the content to the right of (and including) tape 1's head, read as a
binary number with the head cell least significant.

MUL-LIN:  exists J  for all s with |s| = 2m >= 2:
    mt_run(J, s, |code(J)| * (|s| + 1)) halts with output x * y,
    where x = the first m bits of s and y = the last m bits.
This holds iff multitape TMs multiply n-bit integers in time O(n).
"""
import zp_ref as R


def entry(P, idx):
    pc, e = P, 0
    while True:
        if pc <= 1:
            return None
        b = pc & 1
        pc >>= 1
        if b:
            if idx == 0:
                e += 1
        elif idx == 0:
            return e
        else:
            idx -= 1


def mt_run(P, X, t):
    """Output (an int) if the machine halts within t steps, else None."""
    e0 = entry(P, 0)
    if e0 is None:
        return None
    k = e0 + 1
    L = [0] * k
    Rt = [0] * k
    Rt[0] = R.encode_input(X)
    o = 0
    for _ in range(t):
        sym = 0
        for i in range(k):
            sym = 2 * sym + (Rt[i] & 1)
        e = entry(P, 1 + o + sym)
        if e is None:
            return None
        kn, act = divmod(e, 4 ** k)
        if kn == 0:
            return Rt[0]
        o = kn - 1
        for i in reversed(range(k)):
            act, dig = divmod(act, 4)
            w, d = dig & 1, dig >> 1
            if d:
                L[i] = 2 * L[i] + w
                Rt[i] >>= 1
            else:
                Rt[i] = 2 * (2 * (Rt[i] >> 1) + w) + (L[i] & 1)
                L[i] >>= 1
    return None


def correct(J, S):
    n = R.length(S)
    if n == 0 or n % 2:
        return True
    m = n // 2
    x = S - (1 << n)
    return mt_run(J, S, R.length(J) * (n + 1)) == (x >> m) * (x & ((1 << m) - 1))


def mult_beeps(max_beeps=None, candidates=None, max_instances=None):
    cands = iter(candidates) if candidates is not None else R._naturals(1)
    beeps = examined = 0
    for J in cands:
        S = 1
        while True:
            if max_instances is not None and examined >= max_instances:
                return
            examined += 1
            if not correct(J, S):
                yield beeps, J, S
                beeps += 1
                if max_beeps is not None and beeps >= max_beeps:
                    return
                break
            S += 1


def mt_code(k, delta):
    """delta[i][sym] = None (halt) or (acts, nxt), acts = [(w, d)] * k for
    tapes 1..k; state i sits at offset i * 2^k."""
    ents = [k - 1]
    for row in delta:
        for tr in row:
            if tr is None:
                ents.append(0)
            else:
                acts, nxt = tr
                act = 0
                for w, d in acts:
                    act = 4 * act + w + 2 * d
                ents.append(4 ** k * (nxt * 2 ** k + 1) + act)
    bits = []
    for e in ents:
        bits += [1] * e + [0]
    N = 1
    for b in reversed(bits):
        N = 2 * N + b
    return N


# Controlled candidates: right on s = "00" (both erase the input and halt on
# a blank), wrong on the first instance with a nonzero product.
ERASE1 = mt_code(1, [[([(0, 1)], 1), ([(0, 1)], 0)],        # state 0
                     [None, ([(0, 1)], 0)]])                # state 1
ERASE2 = mt_code(2, [[([(0, 1), (1, 0)], 1), None,
                      ([(0, 1), (1, 1)], 0), ([(0, 1), (0, 1)], 0)],
                     [None, ([(0, 1), (0, 0)], 0),
                      ([(0, 1), (0, 1)], 0), None]])
