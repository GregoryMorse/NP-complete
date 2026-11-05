"""Recover native/exact_<name>.json (class -> table state) from machines/<name>.tbl when the
exact-merge output is missing: the table is a quotient of the unmerged compile, so follow transitions.
usage: python3 native/mk_exact_map.py zntt zntt_native"""
import json, os, sys
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
sys.path[:0] = [os.path.join(ROOT, 'native'), os.path.join(ROOT, 'compiler'), os.path.join(ROOT, 'formal')]
import importlib, compile2, final
import gen_logic as G


def main(modname, nat):
    m = importlib.import_module(modname).build()
    sd = final.sides(m, modname)
    t, b, names = compile2.compile_sides(m, final.ENC, sd)
    mm = G.minimize_map(t, b)
    tab, beep = G.read_tbl(nat)
    ncls = max(mm) + 1
    # minimized table over classes
    mt = [None] * ncls
    for s in range(len(t)):
        mt[mm[s]] = [None if tr is None else (tr[0], tr[1], mm[tr[2]]) for tr in t[s]]
    img = {mm[0]: 0}
    queue = [mm[0]]
    while queue:
        c = queue.pop()
        s = img[c]
        for a in (0, 1):
            tr = mt[c][a]
            if tr is None:
                continue
            tt = tab[s][a]
            assert tt is not None and tt[0] == tr[0] and tt[1] == tr[1], (c, s, a, tr, tt)
            if tr[2] in img:
                assert img[tr[2]] == tt[2], ('conflict', c, a)
            else:
                img[tr[2]] = tt[2]
                queue.append(tr[2])
    assert mm[b] in img and img[mm[b]] == beep, 'beep'
    cls = [img.get(c, 0) for c in range(ncls)]
    print(len(img), 'of', ncls, 'classes mapped')
    json.dump(cls, open(os.path.join(ROOT, 'native', f'exact_{nat}.json'), 'w'))


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
