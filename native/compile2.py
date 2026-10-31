"""Compile a 4-symbol logical machine to a 2-symbol TM (cells in pairs)."""
import os
import sys
from itertools import permutations
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'compiler'))
import tm  # noqa: E402


def compile2(m, enc):
    """enc: symbol -> (b1, b2); enc['B'] must be (0, 0)."""
    assert enc['B'] == (0, 0)
    dec = {v: k for k, v in enc.items()}
    names = {}
    table = []

    def st(key):
        if key not in names:
            names[key] = len(table)
            table.append([None, None])
        return names[key]

    qs = m.states()
    for q in qs:
        st(('P', q))
    work = list(qs)
    for q in work:
        p = st(('P', q))
        for x in (0, 1):
            if any((q, dec[(x, y)]) in m.d for y in (0, 1)):
                table[p][x] = (x, 'R', st(('P2', q, x)))
                for y in (0, 1):
                    tr = m.d.get((q, dec[(x, y)]))
                    if tr is None:
                        continue
                    w, d, n = tr
                    x2, y2 = enc[w]
                    if x2 == x and d == 'R':
                        nxt = (y2, 'R', st(('P', n)))
                    elif x2 == x:
                        nxt = (y2, 'L', st(('L1', n)))
                    else:
                        nxt = (y2, 'L', st(('W', x2, d, n)))
                    table[st(('P2', q, x))][y] = nxt
    for key, i in list(names.items()):
        pass
    changed = True
    while changed:
        changed = False
        for key in list(names):
            i = names[key]
            if table[i] != [None, None]:
                continue
            kind = key[0]
            if kind == 'L1':
                table[i] = [(z, 'L', st(('L2', key[1]))) for z in (0, 1)]
            elif kind == 'L2':
                table[i] = [(z, 'L', st(('P', key[1]))) for z in (0, 1)]
            elif kind == 'R1':
                table[i] = [(z, 'R', st(('P', key[1]))) for z in (0, 1)]
            elif kind == 'W':
                _, x2, d, n = key
                nx = st(('R1', n)) if d == 'R' else st(('L2', n))
                table[i] = [(x2, d, nx)] * 2
            else:
                continue
            changed = True
    beep = names[('P', m.beep)]
    return table, beep, names


def best(m):
    res = []
    others = ['M', '0', '1']
    for perm in permutations([(0, 1), (1, 0), (1, 1)]):
        enc = {'B': (0, 0), **dict(zip(others, perm))}
        table, beep, _ = compile2(m, enc)
        mt, mb = tm.minimize(table, beep)
        res.append((len(mt), enc, mt, mb, len(table)))
    res.sort(key=lambda r: r[0])
    return res


def compile_sides(m, enc, side):
    """Side-aware compile: logical state q is entered at cell side[q] of its
    pair (0 = left cell, read rightwards; 1 = right cell, read leftwards)."""
    assert enc['B'] == (0, 0)
    dec = {v: k for k, v in enc.items()}
    names, table = {}, []

    def st(key):
        if key not in names:
            names[key] = len(table)
            table.append(None)
        return names[key]

    def mv(s):
        return 'R' if s > 0 else 'L'

    def goto(delta, n):          # state that is |delta| cells away from n's entry
        return st(('P', n)) if delta == 0 else st(('G', delta, n))

    qs = m.states()
    for q in qs:
        st(('P', q))
    i = 0
    while i < len(table):
        key = [k for k, v in names.items() if v == i][0]
        i += 1
        kind = key[0]
        row = [None, None]
        if kind == 'P':
            q = key[1]
            e = side[q]
            for a in (0, 1):            # first cell read
                syms = [dec[(a, b) if e == 0 else (b, a)] for b in (0, 1)]
                if any((q, s) in m.d for s in syms):
                    row[a] = (a, 'R' if e == 0 else 'L', st(('P2', q, a)))
        elif kind == 'P2':
            _, q, a = key
            e = side[q]
            c = 1 - e                   # we are on the second cell of the pair
            for b in (0, 1):
                sym = dec[(a, b) if e == 0 else (b, a)]
                tr = m.d.get((q, sym))
                if tr is None:
                    continue
                w, d, n = tr
                wv = enc[w]
                T = (2 if d == 'R' else -2) + side[n]
                if wv[1 - c] == a:      # other cell unchanged
                    s = 1 if T > c else -1
                    row[b] = (wv[c], mv(s), goto(T - c - s, n))
                else:
                    o = 1 - c
                    s2 = 1 if T > o else -1
                    row[b] = (wv[c], mv(o - c), st(('W', wv[o], s2, T - o - s2, n)))
        elif kind == 'G':
            _, delta, n = key
            s = 1 if delta > 0 else -1
            row = [(z, mv(s), goto(delta - s, n)) for z in (0, 1)]
        elif kind == 'W':
            _, v, s2, delta, n = key
            row = [(v, mv(s2), goto(delta, n))] * 2
        table[names[key]] = row
    return table, names[('P', m.beep)], names


def default_sides(m):
    cnt = {}
    for (q, s), (w, d, n) in m.d.items():
        cnt.setdefault(n, [0, 0])[d == 'L'] += 1
    return {q: int(cnt.get(q, [1, 0])[1] > cnt.get(q, [1, 0])[0]) for q in m.states()}
