import sys, time, pickle, random
import importlib, compile2, final, tm, exact, dcmin, check2
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 36
budget = int(sys.argv[2]) if len(sys.argv) > 2 else 2_000_000
modname = sys.argv[3] if len(sys.argv) > 3 else 'zp2'
m = importlib.import_module(modname).build(); sd = final.sides(m, modname)
t, b, _ = compile2.compile_sides(m, final.ENC, sd); mt, mb = tm.minimize(t, b)
r = random.Random(seed)
g, gb, mp = dcmin.merge_all(mt, mb, order=None if seed < 0 else (lambda xs: r.sample(xs, len(xs))), ret_map=True)  # seed -1: default order
print('moore', len(mt), 'greedy', len(g), flush=True)
t0 = time.time()
try:
    out, ob, cls = exact.minimize(mt, mb, bound=len(g) - 1, budget=budget, hint=mp, ret_map=True)
except TypeError:
    print('no improvement'); sys.exit()
print(len(out), time.time() - t0, flush=True)
import json; json.dump(cls, open('exact_map_%s_%d.json' % (modname, seed), 'w'))
