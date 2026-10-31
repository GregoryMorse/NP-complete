"""Linear-size linear circuits for the number-theoretic transform (docs/spec.md §2.3).

For n >= 1 let p(n) be the least prime with p = 1 (mod n), and w(n) the least
element of order exactly n in F_p^*.  DFT_n is the n x n matrix W[k][t] = w^(k t)
over F_p.  (Another choice of primitive root permutes the rows, which does not
change circuit size.)  A linear circuit with s gates has inputs x_0..x_{n-1}
(nodes 0..n-1).  Gate i is node n+i = a_i * node u_i + b_i * node v_i, with
u_i, v_i < n+i and a_i, b_i in F_p.  It computes DFT_n if every row of W is the
coefficient vector of some node.

NTT-LIN:  exists c  for all n:  DFT_n over F_p(n) has a circuit with c*n gates.
(Exactly c*n gates covers "at most c*n": spare gates may be redundant.)
This is Σ₂.  It is the finite-field analogue of "the FFT is optimal up to
constants or not": no superlinear lower bound for general linear circuits is known
for any explicit matrix family.
"""
from itertools import product


def is_prime(p):
    return p > 1 and all(p % d for d in range(2, int(p ** .5) + 1))


def params(n):
    p = n + 1
    while not is_prime(p):
        p += n
    for g in range(1, p):
        y, t = g % p, 1
        while y != 1:
            y, t = y * g % p, t + 1
        if t == n:
            return p, g


def has_circuit(n, s):
    """Brute force, enumerating circuits in the same order as the machine."""
    p, w = params(n)
    rows = [tuple(pow(w, k * t, p) for t in range(n)) for k in range(n)]
    choices = [list(product(range(n + i), range(n + i), range(p), range(p)))
               for i in range(s)]
    for circ in product(*choices):
        nodes = [tuple(int(t == j) for t in range(n)) for j in range(n)]
        for (u, v, a, b) in circ:
            nodes.append(tuple((a * x + b * y) % p for x, y in zip(nodes[u], nodes[v])))
        have = set(nodes)
        if all(r in have for r in rows):
            return True
    return False
