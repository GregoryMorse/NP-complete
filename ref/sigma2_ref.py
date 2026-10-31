"""Reference definitions for the further Σ₂ questions (docs/spec.md §2.2).

All use the offset-machine guest of zp_ref.py, extended in two ways:
  * Lt0: initial left part of the tape (nearest cell = least significant bit);
  * window: if given, a move that takes the head more than `window` cells
    from its start cell REJECTs.

MAJ-L (PP-complete)  s in MAJ-L iff more than half of the 2^n certificates c
        of length n = |s| make program s accept within n steps.
L_PS (PSPACE-complete)  s in L_PS iff program s, on the empty input, with
        window n, accepts within 2^(4n+4) steps.
co-L verifiers (NP = coNP)  candidate J is correct on s iff
        [s not in L]  ==  [some Y < 2^T has run(J, rep(s), T, Lt0=Y) = ACC],
        T = (|s|+2)^|code(J)|.
DLOG  s = p||g||h||k, four parts of m bits each (|s| = 4m, m >= 1);
        s in DLOG iff p is prime and g^x = h (mod p) for some 0 <= x <= k.
        Polynomially equivalent to computing discrete logarithms modulo
        primes (binary search on k; primality is in P).
"""
import zp_ref as R

ACC, REJ, TIMEOUT = R.ACC, R.REJ, R.TIMEOUT


def run(P, X, t, Lt0=0, window=None, detect_loops=False):
    Rr = R.encode_input(X)
    Lt = Lt0
    q = 0
    pos = 0
    seen = set() if detect_loops else None
    for _ in range(t):
        if seen is not None:            # exact shortcut: a repeat never halts
            key = (Rr, Lt, q, pos)
            if key in seen:
                return TIMEOUT
            seen.add(key)
        a = Rr & 1
        R1 = Rr >> 1
        e = R.lookup(P, q + a)
        if e is None:
            return REJ
        w, d, k = e
        if k == 0:
            return ACC if w else REJ
        q = k - 1
        if d:
            if window is not None and pos + 1 > window:
                return REJ
            pos += 1
            Lt = 2 * Lt + w
            Rr = R1
        else:
            if window is not None and pos - 1 < -window:
                return REJ
            pos -= 1
            Rr = 2 * (2 * R1 + w) + (Lt & 1)
            Lt >>= 1
    return TIMEOUT


def in_pp(S):
    n = R.length(S)
    acc = sum(run(S, C, n) == ACC for C in range(1 << n, 2 << n))
    return acc > (1 << n) - acc


def in_pspace(S):
    n = R.length(S)
    return run(S, 1, 2 ** (4 * n + 4), window=n, detect_loops=True) == ACC


def is_prime(p):
    return p > 1 and all(p % d for d in range(2, int(p ** .5) + 1))


def in_dlog(S):
    n = R.length(S)
    if n == 0 or n % 4:
        return False
    m = n // 4
    x = S - (1 << n)
    mask = (1 << m) - 1
    p, g, h, k = (x >> 3 * m) & mask, (x >> 2 * m) & mask, (x >> m) & mask, x & mask
    if not is_prime(p):
        return False
    y = 1 % p
    for _ in range(k + 1):
        if y == h % p:
            return True
        y = y * g % p
    return False


def conp_beeps(max_beeps=None, max_instances=None, candidates=None):
    """Z_{NP=coNP}: yields (i, J, S) at each refutation."""
    cands = iter(candidates) if candidates is not None else R._naturals(1)
    beeps = examined = 0
    for J in cands:
        S = 1
        while True:
            if max_instances is not None and examined >= max_instances:
                return
            examined += 1
            T = R.clock(J, S)
            claim = any(run(J, S, T, Lt0=Y) == ACC for Y in range(2 ** T))
            if claim == R.in_L(S):
                yield beeps, J, S
                beeps += 1
                if max_beeps is not None and beeps >= max_beeps:
                    return
                break
            S += 1
