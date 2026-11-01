"""Pick the smallest compiled form of the native machine over merge orders,
using the entry sides found by sides.py (if present)."""
import json
import os
import sys
import zp2
import compile2
import search

ENC = {'B': (0, 0), 'M': (0, 1), '0': (1, 0), '1': (1, 1)}
HERE = os.path.dirname(os.path.abspath(__file__))


def sides(m):
    sd = compile2.default_sides(m)
    p = os.path.join(HERE, 'sides.json')
    if os.path.exists(p):
        saved = json.load(open(p))
        sd.update({q: v for q, v in saved.items() if q in sd})
    return sd


def best(seeds=100):
    m = zp2.build()
    sd = sides(m)
    return min((search.full(m, ENC, sd, seed=k)[0], k) for k in range(seeds))


if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    print(*best(n))
