"""Side local search, parallel objective (min over several merge seeds),
starting from final.sides()."""
import json, random, sys
from multiprocessing import Pool
import importlib, search, final

MOD = sys.argv[4] if len(sys.argv) > 4 else 'zp2'
OUT = 'sides.json' if MOD == 'zp2' else f'sides_{MOD}.json'
M = importlib.import_module(MOD).build()

def one(args):
    sd, k = args
    return search.full(M, final.ENC, sd, seed=k)[0]

def obj(pool, sd, seeds):
    return min(pool.map(one, [(sd, k) for k in seeds]))

if __name__ == '__main__':
    seeds = list(range(int(sys.argv[1]) if len(sys.argv) > 1 else 12))
    passes = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    sd = final.sides(M, MOD)
    rnd = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 0)
    with Pool(4) as pool:
        best = obj(pool, sd, seeds); print('start', best, flush=True)
        qs = M.states()
        for p in range(passes):
            rnd.shuffle(qs)
            for q in qs:
                sd[q] ^= 1
                c = obj(pool, sd, seeds)
                if c <= best:
                    if c < best:
                        print(c, q, flush=True)
                        json.dump(sd, open(OUT, 'w'))
                    best = c
                else:
                    sd[q] ^= 1
    json.dump(sd, open(OUT, 'w'))
    print('final', best)
