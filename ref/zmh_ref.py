"""Reference semantics for the multihead read-only guest (native/zmh.py) and
the L = P machine built on it (native/zlp.py).

Guest model (a multihead two-way DFA, one head at a time):

* A code P is any bit string; R = reverse(P) + '0' and entries  w d 1^k 0
  are parsed exactly as in zp2_ref (rotated once before the first step).
* The input x is read only.  Positions 0 .. n+1 (n = |x|): position 0 is the
  left end marker, n+1 the right one; both read as blank.  Position p in
  1..n reads x[p-1].
* There are |P| + 1 heads, all starting at position 0; the current head is
  head 0.
* One step: read a = the symbol under the current head; rotate R by iota(a);
  if the step budget is used up the run ends with NAC; peek w = R[0],
  d = R[1], t = R[2].  t = 0: halt, ACC iff w = 1.  Otherwise
    w = 1: move the current head right (d = 1) or left (d = 0), staying
           at positions 0 and n+1;
    w = 0: make the next head (d = 1) or the previous head (d = 0) current,
           staying at the last and the first head;
  then rotate past the entry and k + 1 more entries.
* run_mh(P, x, T) is ACC or NAC (a time-out counts as NAC).

A log-space machine is a multihead two-way DFA (Hartmanis 1972); one step of
a k-head automaton costs O(k) steps here (visit every head), and the clock
T = (|x|+2)^(|J|+1) - 1 bounds the polynomial running time once J is padded.
Conversely run_mh(J, x, T) is computed in space O(|J| log |x|).

L = P machine (zlp).  Truth: L_P = { s : run_mh(s, s, |s|+1) = ACC }, the
program s run on its own text with |s|+1 heads.  L_P is in P, and it is
P-complete under log-space reductions: the |s|+1 heads serve as the cells of
a polynomial-time Turing machine's tape (a head at position 0 is a 0, at
position 1 a 1; the current head is the tape head), the input x is written
by the first |x| steps of the program, and padding makes |s|+1 at least the
running time.  So the machine quasihalts iff some J decides L_P within the
clock, iff L_P is in L, iff L = P.
"""
from zp2_ref import ACC, NAC, rot, succ, clock


def run_mh(P, x, T):
    R = rot(P[::-1] + '0')[0]
    n = len(x)
    pos = [0] * (len(P) + 1)
    c = 0
    while True:
        p = pos[c]
        a = None if p == 0 or p == n + 1 else x[p - 1]
        for _ in range({None: 0, '0': 1, '1': 2}[a]):
            R = rot(R)[0]
        if T == 0:
            return NAC
        T -= 1
        w = R[0]
        d = R[1] if len(R) > 1 else '0'
        t = R[2] if len(R) > 2 else '0'
        if t == '0':
            return ACC if w == '1' else NAC
        if w == '1':
            pos[c] = min(p + 1, n + 1) if d == '1' else max(p - 1, 0)
        else:
            c = min(c + 1, len(P)) if d == '1' else max(c - 1, 0)
        R, k = rot(R)
        for _ in range(k + 1):
            R = rot(R)[0]


def in_LP(s):
    return run_mh(s, s, len(s) + 1) == ACC


def correct(J, s, truth=None):
    return (run_mh(J, s, clock(J, s)) == ACC) == (truth or in_LP)(s)


def zp_beeps(truth=None, max_beeps=None, max_instances=None):
    J, beeps, seen = '', 0, 0
    while True:
        s = ''
        while True:
            if max_instances is not None and seen >= max_instances:
                return
            seen += 1
            if not correct(J, s, truth):
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
