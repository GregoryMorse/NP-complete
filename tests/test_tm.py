"""TM backend tests.

1. Lockstep: the non-inlined, unminimised TM is checked against the counter
   machine at *every* counter instruction boundary (state ent<t> on E):
   program counter and all register values must agree.
2. The optimised (inlined + minimised) TM must produce the same beep
   sequence, with the same decoded registers at every beep.
"""
import os
import sys
import random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [os.path.join(HERE, '..', 'ref'), os.path.join(HERE, '..', 'compiler')]

import cm as CMmod                      # noqa: E402
import tm                               # noqa: E402
import zp_cm                            # noqa: E402


def lockstep(prog, order, tm_steps, dec_mode='best'):
    table, info = tm.compile_cm(prog, order, inline=False, dec_mode=dec_mode)
    names = info['names']
    ent_of = {i: int(nm[3:]) for i, nm in enumerate(names) if nm.startswith('ent')}
    regs = {r: 0 for r in prog.regs}
    pc = prog.entry
    checked = 0
    tape = {}
    s, h = 0, 0
    for _ in range(tm_steps):
        if s in ent_of:
            assert ent_of[s] == pc, (ent_of[s], pc)
            assert tape.get(h, 0) == 0
            got = tm.decode_regs(tape, h, order)
            assert got == regs, (pc, got, regs)
            checked += 1
            ins = prog.code[pc]               # advance the counter machine
            if ins[0] == 'INC':
                regs[ins[1]] += 1
                pc = ins[2]
            elif ins[0] == 'DEC':
                if regs[ins[1]]:
                    regs[ins[1]] -= 1
                    pc = ins[2]
                else:
                    pc = ins[3]
            else:
                pc = ins[1]
        tr = table[s][tape.get(h, 0)]
        assert tr is not None, ('undefined transition', s, names[s])
        tape[h] = tr[0]
        h += 1 if tr[1] == 'R' else -1
        s = tr[2]
    return checked


def random_cm(nregs=4, n=40, seed=0):
    """Random terminating-agnostic counter program with one BEEP."""
    rnd = random.Random(seed)
    b = CMmod.CM()
    regs = [f'r{i}' for i in range(nregs)]
    for i in range(n):
        b.label(f'l{i}')
        if i == n // 2:
            b.beep()
        elif rnd.random() < 0.5:
            b.inc(rnd.choice(regs))
        else:
            b.dec(rnd.choice(regs), nz=f'l{rnd.randrange(n)}', z=f'l{rnd.randrange(n)}')
    b.jmp('l0')
    return b.assemble()


def test_lockstep_random():
    for seed in range(30):
        p = random_cm(seed=seed)
        for mode in ('best', 'carry', 'twopass'):
            order = list(p.regs)
            random.Random(seed).shuffle(order)
            lockstep(p, order, 20000, dec_mode=mode)


def test_lockstep_zp():
    p = zp_cm.build().assemble()
    order, _ = tm.optimize_order(p, iters=3000)
    assert lockstep(p, order, 300000) > 1000


def beeps_tm(table, beep, order, n, steps):
    out = []

    def cb(i, tape, h):
        r = tm.decode_regs(tape, h, order, at_E=False)
        out.append((i, r))
        return len(out) < n
    tm.simulate(table, steps, beep=beep, on_beep=cb)
    return out


def test_optimised_matches_cm():
    p = zp_cm.build('nonempty').assemble()
    order, _ = tm.optimize_order(p, iters=3000)
    table, info = tm.compile_cm(p, order)
    mt, mb = tm.minimize(table, info['beep'])
    want = []

    def ob(step, regs):
        want.append(dict(regs))
        return len(want) < 4
    p.run(10**7, on_beep=ob)
    got = beeps_tm(mt, mb, order, 4, 10**8)
    assert [g[1] for g in got] == want[:len(got)] and len(got) >= 3


if __name__ == '__main__':
    test_lockstep_random()
    print('random lockstep ok')
    test_lockstep_zp()
    print('zp lockstep ok')
    test_optimised_matches_cm()
    print('optimised beeps ok')
