"""Reference semantics for the native DLOG machine (native/zdl.py).

Same guest model, clock and enumeration as zp2_ref, and the same instance
encoding as zfac_ref: s is parsed left to right into numbers n_1 .. n_m
('1b' appends digit b, '0' starts the next number).  The last four numbers
are (k, h, g, p) = (n_(m-3), n_(m-2), n_(m-1), n_m); with m = 3, k = 0.

    s in L_D  iff  m >= 3, p is prime and g^e mod p = h for some 0 <= e <= k.

L_D is polynomially equivalent to the discrete logarithm modulo primes
(binary search on k), so the machine quasihalts iff discrete log mod primes
is in P.
"""
from zp2_ref import zp_beeps as _zp_beeps, correct as _correct
from zfac_ref import numbers


def is_prime(p):
    return p >= 2 and all(p % d for d in range(2, p))


def in_LD(s):
    nums = numbers(s)
    if len(nums) < 3:
        return False
    p, g, h = nums[-1], nums[-2], nums[-3]
    k = nums[-4] if len(nums) >= 4 else 0
    if not is_prime(p):
        return False
    y = 1
    for _ in range(k + 1):
        if y == h:
            return True
        y = y * g % p
    return False


def correct(J, s):
    return _correct(J, s, in_LD)


def zp_beeps(max_beeps=None, max_instances=None):
    return _zp_beeps(truth=in_LD, max_beeps=max_beeps, max_instances=max_instances)


if __name__ == '__main__':
    import sys
    print(list(zp_beeps(max_beeps=int(sys.argv[1]) if len(sys.argv) > 1 else 10)))
