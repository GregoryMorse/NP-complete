import random
import sys
import zp2
import compile2
import dcmin
import tm


def cost(m, enc, sd, full=False):
    t, b, _ = compile2.compile_sides(m, enc, sd)
    mt, mb = tm.minimize(t, b)
    if full:
        mt, mb = dcmin.merge_all(mt, mb)
    return len(mt), mt, mb


def search(m, enc, sd, passes=2, seed=0):
    rnd = random.Random(seed)
    best = cost(m, enc, sd)[0]
    qs = m.states()
    for _ in range(passes):
        rnd.shuffle(qs)
        for q in qs:
            sd[q] ^= 1
            c = cost(m, enc, sd)[0]
            if c <= best:
                best = c
            else:
                sd[q] ^= 1
    return best, sd


if __name__ == '__main__':
    m = zp2.build()
    enc = {'B': (0, 0), 'M': (0, 1), '0': (1, 0), '1': (1, 1)}
    sd = compile2.default_sides(m)
    b, sd = search(m, enc, sd)
    print('moore', b, 'full', cost(m, enc, sd, True)[0])
