"""Instance tests for the NP = coNP machine (C logical simulator vs reference).
Only pairs whose reference search needs at most CAP runs are used."""
import sys, random, time
sys.path.insert(0, '../ref')
import zconp, zconp_ref, clsim
from zp2_ref import clock
CAP = 300
MULTI = False

def feasible(J, s):
    try:
        a, b = {'cap': CAP}, {'cap': CAP}
        t = zconp_ref.run_nd(s, '', len(s) + 1, a) == zconp_ref.ACC
        r = zconp_ref.run_nd(J, s, clock(J, s), b) == zconp_ref.ACC
        if MULTI and a['runs'] + b['runs'] < 4:
            return None
        return r != t
    except OverflowError:
        return None

if __name__ == '__main__':
    m = zconp.build(); ix = clsim.write_table(m, '/tmp/zc.ltab')
    rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    maxJ = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    MULTI = len(sys.argv) > 4
    bad = done = 0
    while done < N:
        J = ''.join(rnd.choice('01') for _ in range(rnd.randint(0, maxJ)))
        s = ''.join(rnd.choice('01') for _ in range(rnd.randint(0, 4)))
        want = feasible(J, s)
        if want is None:
            continue
        t0 = time.time()
        got = clsim.instance('/tmp/zc.ltab', ix, m.beep, J, s, 4 * 10**9)
        done += 1; bad += got != want
        print(J, s, got, want, 'BAD' if got != want else '', round(time.time() - t0, 1), flush=True)
    print('bad', bad, 'of', done)
