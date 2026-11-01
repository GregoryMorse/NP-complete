"""Reference semantics for the native GI machine (native/zgi.py).

Same guest model, clock and enumeration as zp2_ref (Z_P v2).  Only the
language changes: the truth bit is computed natively by brute force.

Instance encoding (unary).  Split s at its 0s into runs of 1s and read the
run lengths last to first: T = [m, X_1, X_2, ..., 0, H_1, H_2, ..., 0, ...].
m is the last run, X the runs before it down to the first empty run, H the
runs before that down to the next empty run (or to the start of s); anything
further is ignored.

    X    a directed graph as an edge list of labels: edges (X_1, X_2), (X_3, X_4) ..
    H    an adjacency matrix with rows of width m, flattened: H_k with k = (a-1) m + b
         is the entry for the edge (a, b); an entry is an edge iff it is >= 2.

    s in L_GI  iff  some injective w: {1..t} -> {1..m} (t <= m) maps the edges
                    of X one-to-one onto the edges of H: every label of X is
                    <= t, the entries k(w x, w y) of the edges (x, y) of X
                    exist, are edges and are pairwise distinct, and they are
                    all the edges of H.

L_GI is polynomially equivalent to graph isomorphism: for digraphs G, H on
{1..n} without isolated vertices, (X = edges of G, m = n, H) is in L_GI iff
G ~ H; conversely, s is in L_GI iff X has an even number of labels and no
repeated edge, every edge of H lies in {1..m}^2, X uses at most m labels
(after renaming them to 1..t) and the two edge sets are isomorphic, which
a GI oracle decides (both graphs taken without isolated vertices).
"""
from itertools import permutations

from zp2_ref import zp_beeps as _zp_beeps, correct as _correct


def parse(s):
    T = [len(r) for r in reversed(s.split('0'))]
    m, rest = T[0], T[1:]
    X = rest[:rest.index(0)] if 0 in rest else rest
    rest = rest[len(X) + 1:]
    H = rest[:rest.index(0)] if 0 in rest else rest
    return m, X, H


def check(w, m, X, H):
    if len(X) % 2:
        return False
    used = set()
    for x, y in zip(X[::2], X[1::2]):
        if x > len(w) or y > len(w):
            return False
        k = (w[x - 1] - 1) * m + w[y - 1]
        if k > len(H) or H[k - 1] < 2 or k in used:
            return False
        used.add(k)
    return all(k + 1 in used for k, e in enumerate(H) if e >= 2)


def in_LG(s):
    m, X, H = parse(s)
    return any(check(w, m, X, H) for t in range(m + 1)
               for w in permutations(range(1, m + 1), t))


def correct(J, s):
    return _correct(J, s, in_LG)


def zp_beeps(max_beeps=None, max_instances=None):
    return _zp_beeps(truth=in_LG, max_beeps=max_beeps, max_instances=max_instances)


if __name__ == '__main__':
    import sys
    print(list(zp_beeps(max_beeps=int(sys.argv[1]) if len(sys.argv) > 1 else 10)))
