"""par.py for any machine module: python3 parx.py MODULE N"""
import sys, importlib, final, search
from multiprocessing import Pool
mod = importlib.import_module(sys.argv[1])
def f(k):
    m = mod.build(); sd = final.sides(m, sys.argv[1])
    return (search.full(m, final.ENC, sd, seed=k)[0], k)
if __name__ == '__main__':
    with Pool(int(sys.argv[3]) if len(sys.argv) > 3 else 1) as p:
        r = sorted(p.map(f, range(int(sys.argv[2]))))
    print(r[:6])
