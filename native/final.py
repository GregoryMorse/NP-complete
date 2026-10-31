"""Pick the smallest compiled form of the native machine over merge orders."""
import json
import sys
import zp2
import compile2
import search

ENC = {'B': (0, 0), 'M': (0, 1), '0': (1, 0), '1': (1, 1)}


def best(seeds=100):
    m = zp2.build()
    sd = compile2.default_sides(m)
    res = min((search.full(m, ENC, sd, seed=k)[0], k) for k in range(seeds))
    return res


if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    c, k = best(n)
    print(c, k)
    json.dump({'states': c, 'seed': k}, open('best_seed.json', 'w'))
