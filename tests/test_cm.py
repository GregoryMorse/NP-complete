"""Counter-machine program vs. Python reference: beep sequences must agree."""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [os.path.join(HERE, '..', 'ref'), os.path.join(HERE, '..', 'compiler')]

import zp_ref as R                      # noqa: E402
import zp_cm                            # noqa: E402

TRUTHS = {
    'L': None,
    'nonempty': lambda S: S > 1,
    'odd': lambda S: S > 1 and S & 1 == 1,
}


def cm_beeps(truth, candidates, nbeeps, max_steps):
    prog = zp_cm.build(truth, candidates).assemble()
    out = []

    def on_beep(step, regs):
        out.append((len(out), regs['J'], regs['S']))
        return len(out) < nbeeps
    steps, regs, pc = prog.run(max_steps, on_beep=on_beep)
    return out, steps


def ref_beeps(truth, candidates, nbeeps, max_inst=20000):
    return list(R.zp_beeps(truth=TRUTHS[truth], candidates=candidates,
                           max_beeps=nbeeps, max_instances=max_inst))


def check(truth, candidates=None, nbeeps=10, max_steps=10**8):
    want = ref_beeps(truth, candidates, nbeeps)
    got, steps = cm_beeps(truth, candidates, nbeeps, max_steps)
    assert got == want[:len(got)], (truth, got, want)
    return got, want, steps


def test_real_prefix():
    got, want, _ = check('L', nbeeps=6, max_steps=3 * 10**7)
    assert len(got) >= 3


def test_pswap_nonempty_full_enumeration():
    # The first correct candidate for L' = {s != eps} is reached; beeps stop.
    want = ref_beeps('nonempty', None, 10**6)
    got, steps = cm_beeps('nonempty', None, 10**6, 4 * 10**7)
    assert got == want


def test_controlled():
    # known-wrong candidates followed by a known-correct one for 'odd'
    wrong = [1, R.assemble([(1, 1, 0)] * 3), R.assemble([(0, 1, 0), (0, 1, 0)])]
    good = R.assemble([(0, 0, 0), (1, 0, 0)])  # accept iff first cell is 1
    cands = wrong + [good]
    want = ref_beeps('nonempty', cands, 100)
    got, _ = cm_beeps('nonempty', cands, 100, 10**7)
    assert got == want


if __name__ == '__main__':
    for t in ('nonempty', 'odd'):
        want = ref_beeps(t, None, 10**6)
        print(t, 'reference beeps:', len(want), 'last:', want[-1] if want else None)
        got, steps = cm_beeps(t, None, 10**6, 2 * 10**8)
        print(t, 'counter  beeps:', len(got), 'steps', steps, 'match', got == want)
    got, want, steps = check('L', nbeeps=8, max_steps=10**8)
    print('L', got, steps)
