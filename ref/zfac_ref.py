"""Reference semantics for the native FACTOR machine (native/zfac.py).

Same guest model, clock and enumeration as zp2_ref (Z_P v2).  Only the
language changes: the truth bit is computed natively by brute force.

Instance encoding.  Parse s, left to right, into
numbers (binary, most significant digit first): a pair '1b' appends digit b to
the current number, a '0' starts the next number, a trailing lone '1' is
ignored.  k is the first number and a the second (empty = 0); later numbers
are ignored.

    s in L_F  iff  s has at least two numbers and some d with 2 <= d <= k
                   divides a.

L_F is polynomially equivalent to factoring: (a, min(k, a-1)) asks whether a
has a nontrivial divisor <= k (binary search on k finds the least prime
factor), and conversely L_F is decided by factoring a.  So the machine
quasihalts iff some J decides L_F within the clock, iff factoring is in P.
"""
from zp2_ref import zp_beeps as _zp_beeps, correct as _correct


def numbers(s):
    r = s
    nums, i = [''], 0
    while i < len(r):
        if r[i] == '1':
            if i + 1 == len(r):
                break
            nums[-1] += r[i + 1]
            i += 2
        else:
            nums.append('')
            i += 1
    return [int(x, 2) if x else 0 for x in nums]


def in_LF(s):
    nums = numbers(s)
    if len(nums) < 2:
        return False
    k, a = nums[0], nums[1]
    return any(a % d == 0 for d in range(2, k + 1))


def correct(J, s):
    return _correct(J, s, in_LF)


def zp_beeps(max_beeps=None, max_instances=None):
    return _zp_beeps(truth=in_LF, max_beeps=max_beeps, max_instances=max_instances)


if __name__ == '__main__':
    import sys
    print(list(zp_beeps(max_beeps=int(sys.argv[1]) if len(sys.argv) > 1 else 10)))
