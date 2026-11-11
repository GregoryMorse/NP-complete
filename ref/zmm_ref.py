"""Reference semantics for the native GF(2) matrix-product machine (native/zmm.py).

Guest model, clock and outer loop: those of zmul_ref (Z_P v2 plus a queue of
|J| stacks, T = (|s|+2) * 2^|J| - 1, every run a decider run, a beep on the
first s on which J is wrong).  Only the truth of a proper halt changes.

Instance:  s = 1^m 0 w  (m = the number of leading 1s; if s has no 0, w = '').
* B = w[0 : m^2] as an m x m matrix, row-major, padded with 0s;
* A = w[m^2 :] cut into rows of length m (the last row padded with 0s), so A
  has r = ceil(|A| / m) rows (r = 0 when m = 0);
* C = A B over GF(2), r x m, row-major.
J is correct on s iff the run halts properly within T and out, padded with 0s,
starts with C.  (out may be longer; if |w| <= m^2, C is empty.)

The machine quasihalts iff some multitape Turing machine computes the GF(2)
product of two m x m matrices in time O(m^2) (linear in the input):
* the guest model and multitape machines simulate each other in linear time
  (zmul_ref);
* this encoding and the plain one (1^m 0 A B, A and B m x m) convert into each
  other in linear time; an r x m times m x m product is ceil(r/m) square
  products (r >= m) or one square product with A padded (r < m), and in both
  cases the input has at least max(m^2, r m) cells.
"""
from zmul_ref import run, clock
from zp2_ref import succ


def parse(s):
    """(m, A rows, B rows) of s."""
    m = len(s) - len(s.lstrip('1'))
    w = s[m + 1:]
    if m == 0:
        return 0, [], []
    Bf = (w[:m * m] + '0' * (m * m))[:m * m]
    Af = w[m * m:]
    r = -(-len(Af) // m)
    Af = Af + '0' * (r * m - len(Af))
    return m, [Af[i * m:(i + 1) * m] for i in range(r)], [Bf[k * m:(k + 1) * m] for k in range(m)]


def product(s):
    """C = A B over GF(2), flattened row-major."""
    m, A, B = parse(s)
    out = []
    for row in A:
        acc = [0] * m
        for k in range(m):
            if row[k] == '1':
                acc = [x ^ int(y) for x, y in zip(acc, B[k])]
        out.extend(acc)
    return ''.join(map(str, out))


def check(out, s):
    C = product(s)
    return (out + '0' * len(C))[:len(C)] == C


def correct(J, s):
    out = run(J, s, clock(J, s), len(J))
    return out is not None and check(out, s)


def zp_beeps(max_beeps=None, max_instances=None):
    """Yield (beep index, J, s) for each refutation, in machine order."""
    J, beeps, seen = '', 0, 0
    while True:
        s = ''
        while True:
            if max_instances is not None and seen >= max_instances:
                return
            seen += 1
            if not correct(J, s):
                yield beeps, J, s
                beeps += 1
                if max_beeps is not None and beeps >= max_beeps:
                    return
                break
            s = succ(s)
        J = succ(J)


if __name__ == '__main__':
    import sys
    print(list(zp_beeps(max_beeps=int(sys.argv[1]) if len(sys.argv) > 1 else 10)))
