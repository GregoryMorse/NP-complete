"""Multitape interpreter of compiler/mult_cm.py vs ref/mult_ref.py.

Probe mode: for each fixed small code J, the counter program beeps with the
output register at every halting run.  The (S, output) sequence must match
mt_run on every even-length instance; odd instances are skipped by both.
Then the real machine's beeps are compared with mult_beeps."""
import os
import random
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [os.path.join(HERE, '..', 'compiler'), os.path.join(HERE, '..', 'ref')]
import mult_cm                 # noqa: E402
import mult_ref as M           # noqa: E402
import zp_ref as R             # noqa: E402


def probe(J, smax):
    p = mult_cm.build(candidates=[J], probe=True).assemble()
    got = []
    seen = {}

    def ob(step, regs):
        got.append((regs['S'], regs['V']))
        return regs['S'] < smax
    seen['steps'] = p.run(2 * 10**7, on_beep=ob)[0]
    want = []
    for S in range(1, smax + 1):
        n = R.length(S)
        if n and n % 2 == 0:
            out = M.mt_run(J, S, R.length(J) * (n + 1))
            if out is not None:
                want.append((S, out))
    k = min(len(got), len(want))
    return got[:k] == want[:k] and k > 0, k


def main():
    random.seed(7)
    ok, halts, tried = True, 0, 0
    for J in [2, 3, 4, 5, 6, 10, 12, 20, 40] + random.sample(range(7, 1 << 11), 60):
        good, k = probe(J, 40)
        tried += 1
        if k:
            halts += k
            ok &= good
            if not good:
                print('MISMATCH', J)
    p = mult_cm.build().assemble()
    got = []
    p.run(10**8, on_beep=lambda st, r: got.append((r['J'], r['S'])) or len(got) < 20)
    want = [(J, S) for _, J, S in M.mult_beeps(max_beeps=len(got))]
    ok &= got == want
    print(f'probe: {tried} codes, {halts} halting runs compared; real machine: '
          f'{len(got)} beeps -> {"OK" if ok else "FAIL"}')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
