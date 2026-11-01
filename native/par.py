import sys, zp2, final, search
from multiprocessing import Pool
def f(k):
    m = zp2.build(); sd = final.sides(m)
    return (search.full(m, final.ENC, sd, seed=k)[0], k)
if __name__ == '__main__':
    n = int(sys.argv[1])
    with Pool(4) as p:
        r = sorted(p.map(f, range(n)))
    print(r[:8])
