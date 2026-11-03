"""Reference semantics for the native NTT machine (native/zntt.py).

Native statement (equivalent to NTT-LIN of docs/spec.md, constants aside):

  exists c  for all n >= 1:  with p the least prime = 1 (mod n) and N = c*n,
  some *chain circuit* of N records over F_p computes DFT_n up to a diagonal.

A chain circuit has records 0 .. N-1.  Record j holds a pointer u_j in
{none, 0, .., j-1} and a coefficient b_j in F_p, and computes

    node_j = [j < n] x_j  +  node_{j-1}  +  b_j * node_{u_j}      (node_{-1} = 0).

The outputs are the last n records.  Output k has the root z_k = b_k (its own
coefficient) and must compute the row (z_k^t)_{t<n}; the power sums
s_t = sum_k z_k^t must vanish for 0 < t < n, and s_n must not.  Since p > n,
Newton's identities make the z_k the n roots of x^n = c for one c != 0, which
are distinct.  So the output matrix is V = DFT_n * diag(zeta^t) (zeta^n = c), with
its rows in some order.

Equivalence with NTT-LIN (fan-in 2 gates a*u + b*v, rows in any order):
* a gate g = a x + b y becomes three records  0 (= prev + (p-1) prev),
  then + a x, then + b y;  inputs are records x_j + prev - prev;  output k is
  out_{k-1} + z_k * h_k with h_k = (row_k - out_{k-1}) / z_k, two gates;
  padding records are  prev + 0.  So c gates per input give O(c) n records.
* conversely a record is at most two fan-in 2 gates, and the diagonal
  diag(zeta^t) and its inverse cost n gates each.

The machine starts at c = 1, n = 1.  For each (c, n) it runs through all (u, b)
of all records (an odometer).  If it finds a circuit it moves to n + 1.
Otherwise it beeps and moves to c + 1, keeping n.  This is sound because a
circuit for (c, n) with c >= 2 gives one for (c + 1, n): insert n records
prev + 0 after the inputs.  A c = 1 circuit gives one for any c >= 6.  So the
machine quasihalts iff NTT-LIN holds.
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
    """recs: list of (u, b), u None for none; an output's root is its b.
    True iff output k computes the row (z_k^t)_{t<n} and the power sums
    s_t = sum_k z_k^t vanish for 0 < t < n while s_n does not."""
    N = len(recs)
    zs = [b for _, b in recs[N - n:]]
    E = [1] * n
    for t in range(n):
        val = []
        for j, (u, b) in enumerate(recs):
            v = int(j == t) + (val[j - 1] if j else 0)
            if u is not None and u < j:
                v += b * val[u]
            val.append(v % p)
        for k in range(n):
            if val[N - n + k] != E[k]:
                return False
            E[k] = E[k] * zs[k] % p
        if (sum(E) % p == 0) == (t == n - 1):
            return False
    return True


def has_circuit(c, n):
    p, N = prime(n), c * n
    return any(evaluate(n, p, list(recs)) for recs in
               product(*[product([None] + list(range(j)), range(p)) for j in range(N)]))


def zp_beeps(max_beeps=None):
    """Yield (beep index, c, n) for each refutation (machine order: n is kept)."""
    c, n, beeps = 1, 1, 0
    while max_beeps is None or beeps < max_beeps:
        if has_circuit(c, n):
            n += 1
        else:
            yield beeps, c, n
            beeps += 1
            c += 1


if __name__ == '__main__':
    print(has_circuit(1, 1), has_circuit(1, 2), has_circuit(2, 1))
