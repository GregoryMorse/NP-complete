"""Reference definitions of the NP-intermediate candidate languages.

Instances are bitstrings s with rep(s) = S = int('1'+s, 2), n = |s|, and
x = S - 2^n = int(s, 2) (leading zeros allowed).  Every string is an
instance, and malformed strings are simply not in the language.

FACTOR  n = 2m, m >= 1.  a = x >> m (the first m bits), k = x mod 2^m (the
        last m bits).  s in FACTOR  iff  a has a divisor d with 2 <= d <= k
        and d < a.
        Polynomially equivalent (both ways) to the standard decision version
        of integer factoring: pad k with leading zeros to the length of a.
        FACTOR in P  iff  integers can be factored in polynomial time
        (binary search on k).

DIGRAPH-ISO  n = 2 m^2, m >= 1.  H[i][j] = bit i*m+j of x and
        G[i][j] = bit m^2+i*m+j of x (bit 0 = least significant = last
        character of s): two m-vertex directed graphs, loops allowed.
        s in DIGRAPH-ISO  iff  some permutation p of {0..m-1} has
        G[i][j] = H[p(i)][p(j)] for all i, j.
        Isomorphism of directed graphs is polynomially equivalent to graph
        isomorphism (GI-complete), so DIGRAPH-ISO in P iff GI in P.
"""
from itertools import permutations


def _split(S):
    n = S.bit_length() - 1
    return n, S - (1 << n)


def in_factor(S):
    n, x = _split(S)
    if n == 0 or n % 2:
        return False
    m = n // 2
    a, k = x >> m, x & ((1 << m) - 1)
    return any(a % d == 0 for d in range(2, min(k, a - 1) + 1))


def in_gi(S):
    n, x = _split(S)
    m = 1
    while 2 * m * m < n:
        m += 1
    if 2 * m * m != n:
        return False
    bit = lambda t: (x >> t) & 1                                  # noqa: E731
    return any(all(bit(m * m + i * m + j) == bit(p[i] * m + p[j])
                   for i in range(m) for j in range(m))
               for p in permutations(range(m)))


from sigma2_ref import in_dlog  # noqa: E402

TRUTHS = {'factor': in_factor, 'gi': in_gi, 'dlog': in_dlog}
