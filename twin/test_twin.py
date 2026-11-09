"""Checks for the native twin-prime beeper (run: python3 twin/test_twin.py).

1. machines/twinprime_native.* are what export.py writes from design.py.
2. Round model: every entry to G2 is a walk start  K(m, d) = 1^(d-1) 0 0 1^(m-d)  (head on R's first
   cell) or, when R is empty, the beep  1^(d-1) 0 0  with d = m; the sequence of (m, d) is the
   trial-division order: m = 3, 4, ..; for each m, d = 2, 3, .. up to the first d with d | m or
   d | m + 2 (fail), or through d = m (every d passed: beep).  Checked for m < M.
3. BP is entered exactly at the beeps, and the beeps are the lesser twin primes, in order.
"""
import os, sys, tempfile, filecmp
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from design import T, START, BEEP, lesser_twins
import export


def model(M):
    """(m, d, beep) for every G2 entry, in order, for m < M."""
    out = []
    for m in range(3, M):
        for d in range(2, m + 1):
            if d == m:
                out.append((m, d, True))
                break
            out.append((m, d, False))
            if m % d == 0 or (m + 2) % d == 0:
                break
    return out


def trace(M):
    tape, h, q, seen, beeps = {}, 0, START, [], []
    exp = model(M)
    while len(seen) < len(exp):
        if q == 'G2':
            lo = min(k for k, v in tape.items() if v) if any(tape.values()) else h
            hi = max(k for k, v in tape.items() if v)
            s = ''.join(str(tape.get(i, 0)) for i in range(lo, max(hi, h) + 1))
            seen.append((s, h - lo))
        if q == BEEP:
            beeps.append(len(seen))
        a = tape.get(h, 0)
        w, mv, q = T[q][a]
        tape[h] = w
        h += 1 if mv == 'R' else -1
    return exp, seen, beeps


def main():
    with tempfile.TemporaryDirectory() as tmp:
        export.main(tmp)
        for ext in ('txt', 'tbl', 'json'):
            f = f'twinprime_native.{ext}'
            assert filecmp.cmp(os.path.join(tmp, f), os.path.join(HERE, '..', 'machines', f), shallow=False), f
    M = 90
    exp, seen, beeps = trace(M)
    for (m, d, b), (s, off) in zip(exp, seen):
        want = '1' * (d - 1) + '00' + '1' * (m - d)
        assert s.rstrip('0') == want.rstrip('0') and off == d + 1, (m, d, s, off)
    # the BP visit after G2 entry i (1-based count) is the beep of that entry
    got = [exp[i - 1][0] for i in beeps]
    assert all(exp[i - 1][2] for i in beeps) and len(beeps) == sum(b for *_, b in exp)
    assert got == lesser_twins(len(got)), got
    print(f'ok: {len(exp)} rounds for m < {M}, beeps at {got}')


if __name__ == '__main__':
    main()
