import random, sys, json
from itertools import permutations
import zp2, compile2, dcmin, tm


def full(m, enc, sd, seed=None):
    t, b, _ = compile2.compile_sides(m, enc, sd)
    mt, mb = tm.minimize(t, b)
    order = None
    if seed is not None:
        r = random.Random(seed)
        order = lambda xs: r.sample(xs, len(xs))
    mt, mb = dcmin.merge_all(mt, mb, order=order)
    return len(mt), mt, mb


def main(seed=0, passes=2):
    m = zp2.build()
    rnd = random.Random(seed)
    best = None
    for perm in permutations([(0, 1), (1, 0), (1, 1)]):
        enc = {'B': (0, 0), 'M': perm[0], '0': perm[1], '1': perm[2]}
        sd = compile2.default_sides(m)
        c = full(m, enc, sd)[0]
        qs = m.states()
        for _ in range(passes):
            rnd.shuffle(qs)
            for q in qs:
                sd[q] ^= 1
                c2 = full(m, enc, sd)[0]
                if c2 <= c:
                    c = c2
                else:
                    sd[q] ^= 1
        print(c, enc, flush=True)
        if best is None or c < best[0]:
            best = (c, enc, dict(sd))
    json.dump({'states': best[0], 'enc': {k: list(v) for k, v in best[1].items()}, 'sides': best[2]},
              open('best_sides.json', 'w'))


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
