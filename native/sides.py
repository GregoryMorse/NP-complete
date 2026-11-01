"""Local search over pair entry sides; objective = best of a few merge seeds."""
import json, random, sys
import zp2, compile2, search, final


def obj(m, sd, seeds=(0, 1, 2)):
    return min(search.full(m, final.ENC, sd, seed=k)[0] for k in seeds)


def run(passes=2, seed=0):
    m = zp2.build()
    sd = compile2.default_sides(m)
    best = obj(m, sd)
    rnd = random.Random(seed)
    qs = m.states()
    for p in range(passes):
        rnd.shuffle(qs)
        for q in qs:
            sd[q] ^= 1
            c = obj(m, sd)
            if c <= best:
                if c < best:
                    print(c, flush=True)
                best = c
            else:
                sd[q] ^= 1
    json.dump(sd, open('sides.json', 'w'))
    return best


if __name__ == '__main__':
    print('final', run())
