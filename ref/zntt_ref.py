"""Reference semantics for the native NTT machine (native/zntt.py).

Native statement (equivalent to NTT-LIN of docs/spec.md, constants aside):

  exists c  for all n >= 1:  with p the least prime = 1 (mod n) and N = c*n,
  some *chain circuit* of N records over F_p computes DFT_n.

A chain circuit has records 0 .. N-1.  Record j holds a pointer u_j in
{none, 0, .., N-2}, a coefficient b_j in F_p and a root z_j in F_p, and computes

    node_j = [j < n] x_j  +  node_{j-1}  +  b_j * node_{u_j}

(node_{-1} = 0; a pointer that is none or >= j contributes 0).  The outputs are the
last n records; output k must have row (z_k^t)_{t<n}, with z_k^n = 1 and
z_{N-n} < .. < z_{N-1}.  So the outputs are the n distinct n-th roots of unity,
i.e. the rows of DFT_n in increasing order of their root.

Equivalence with NTT-LIN (fan-in 2 gates a*u + b*v, rows in any order):
* a gate g = a x + b y becomes three records  0 (= prev + (p-1) prev),
  then + a x, then + b y;  inputs are records x_j + prev - prev;  every row
  is copied to an output by  0, then + 1 row;  padding records are  prev + 0.
  So c gates per input give at most (3c + 3) n records.
* conversely a record is at most two fan-in 2 gates.

The machine enumerates c = 1, 2, .. and for each c, n = 1, 2, ..; for each
(c, n) it runs through all (u, b, z) of all records (an odometer) and moves to
n + 1 when a circuit is found.  When none exists it beeps and moves to c + 1,
n = 1.  It quasihalts iff NTT-LIN holds.
"""
from itertools import product


def is_prime(p):
    return p > 1 and all(p % d for d in range(2, int(p ** .5) + 1))


def prime(n):
    p = n + 1
    while not is_prime(p):
        p += n
    return p


def evaluate(n, p, recs):
    """recs: list of (u, b, z), u None for none.  True iff it computes DFT_n."""
    N = len(recs)
    outs = recs[N - n:]
    if any(outs[i][2] >= outs[i + 1][2] for i in range(n - 1)):
        return False
    E = [1] * n
    for t in range(n):
        val = []
        for j, (u, b, z) in enumerate(recs):
            v = int(j == t) + (val[j - 1] if j else 0)
            if u is not None and u < j:
                v += b * val[u]
            val.append(v % p)
        for k in range(n):
            if val[N - n + k] != E[k]:
                return False
            E[k] = E[k] * outs[k][2] % p
    return all(e == 1 for e in E)


def has_circuit(c, n):
    p, N = prime(n), c * n
    one = list(product([None] + list(range(N - 1)), range(p), range(p)))
    return any(evaluate(n, p, list(recs)) for recs in product(one, repeat=N))


def zp_beeps(max_beeps=None):
    """Yield (beep index, c, n) for each refuted c (machine order)."""
    c, beeps = 1, 0
    while max_beeps is None or beeps < max_beeps:
        n = 1
        while has_circuit(c, n):
            n += 1
        yield beeps, c, n
        beeps += 1
        c += 1


if __name__ == '__main__':
    print(has_circuit(1, 1), has_circuit(1, 2), has_circuit(2, 1))
