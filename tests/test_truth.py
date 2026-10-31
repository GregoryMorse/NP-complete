"""Brute-force truth routines (compiler/truth_cm.py) vs ref/np_intermediate.py.

The harness program enumerates S = 1, 2, ... and beeps iff S is in the
language; the beep sequence must be exactly the members, and every
temporary must be 0 at each beep."""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [os.path.join(HERE, '..', 'compiler'), os.path.join(HERE, '..', 'ref')]
import truth_cm                 # noqa: E402
import np_intermediate as NI    # noqa: E402


def check(name, members):
    p = truth_cm.harness(name).assemble()
    got = []

    def ob(step, regs):
        bad = [r for r, v in regs.items() if v and r not in ('S', 'N')]
        assert not bad, (name, regs['S'], bad)
        got.append(regs['S'])
        return len(got) < members
    p.run(10**11, on_beep=ob)
    want, S = [], 1
    while len(want) < len(got):
        if NI.TRUTHS[name](S):
            want.append(S)
        S += 1
    ok = got == want
    print(f'{name:8s} {len(p)} instructions, first {len(got)} members up to S={got[-1]} '
          f'-> {"OK" if ok else "FAIL"}')
    return ok


if __name__ == '__main__':
    ok = check('factor', 200)
    ok &= check('gi', 30)
    sys.exit(0 if ok else 1)
