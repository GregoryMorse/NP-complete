import sys, time, pickle, random
import zp2, compile2, final, tm, exact, dcmin, check2
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 36
budget = int(sys.argv[2]) if len(sys.argv) > 2 else 2_000_000
m = zp2.build(); sd = final.sides(m)
t, b, _ = compile2.compile_sides(m, final.ENC, sd); mt, mb = tm.minimize(t, b)
r = random.Random(seed)
g, gb, mp = dcmin.merge_all(mt, mb, order=lambda xs: r.sample(xs, len(xs)), ret_map=True)
print('moore', len(mt), 'greedy', len(g), flush=True)
t0 = time.time()
try:
    out, ob = exact.minimize(mt, mb, bound=len(g) - 1, budget=budget, hint=mp)
except TypeError:
    print('no improvement'); sys.exit()
print(len(out), time.time() - t0, flush=True)
ok, got, want = check2.check(out, ob, final.ENC, 40); print(ok)
pickle.dump((out, ob), open('exact_best_%d.pkl' % seed, 'wb'))
