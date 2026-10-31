"""Coalescing soundness: original and coalesced counter programs run in
lockstep; every physical register must equal the sum of its class."""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [os.path.join(HERE, '..', 'ref'), os.path.join(HERE, '..', 'compiler')]
import regalloc   # noqa: E402
import zp_cm      # noqa: E402
import twin_cm    # noqa: E402


def lockstep(vprog, pinned, steps, iters=3000):
    prog, order, _, classes = regalloc.allocate(vprog, pinned=pinned, iters=iters, restarts=1)
    cls = {next(r for r in order if r in c): c for c in classes}
    v = {r: 0 for r in vprog.regs}
    ph = {r: 0 for r in prog.regs}
    pc = vprog.entry
    for _ in range(steps):
        for name, c in cls.items():
            if name in ph:
                assert ph[name] == sum(v[r] for r in c), (pc, name)
        a, b = vprog.code[pc], prog.code[pc]
        assert a[0] == b[0] and a[2:] == b[2:]
        if a[0] == 'INC':
            v[a[1]] += 1
            ph[b[1]] += 1
            pc = a[2]
        elif a[0] == 'DEC':
            za, zb = v[a[1]] == 0, ph[b[1]] == 0
            assert za == zb, ('zero test differs', pc, a[1], b[1])
            if not za:
                v[a[1]] -= 1
                ph[b[1]] -= 1
                pc = a[2]
            else:
                pc = a[3]
        else:
            pc = a[1]


def test_zp():
    for t in ('L', 'nonempty', 'odd'):
        lockstep(zp_cm.build(t).assemble(), ('J', 'S'), 2 * 10**6)


def test_twin():
    lockstep(twin_cm.build().assemble(), ('M',), 10**6)


if __name__ == '__main__':
    test_zp()
    test_twin()
    print('regalloc lockstep ok')
