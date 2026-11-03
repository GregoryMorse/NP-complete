#!/usr/bin/env python3
"""Python mirror of formal/ZP/SymExec.lean, for designing segment checks.

Loads zpLogic from formal/ZP/Logic.lean.  Items: ('s', a) or ('b', i, f) with
f = 'id' or an int (constant).  SC = (q, l, r, dirL) with l nearest first.
"""
import os, re

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = open(os.path.join(HERE, '..', 'ZP', 'Logic.lean')).read()


def _rows():
    rows = []
    for k in range(5):
        m = re.search(r'def zpLogicRows%d : List \(List Nat\) :=\s*\[(.*?)\]\n' % k, SRC, re.S)
        body = m.group(1)
        rows += [list(map(int, x.split(','))) for x in re.findall(r'\[([0-9, ]+)\]', body)]
    return rows


TABLE = _rows()
BEEP = int(re.search(r'def zpLogic : LTM := ⟨zpLogicRows, (\d+)⟩', SRC).group(1))
Q = {n: int(v) for n, v in re.findall(r'def (\w+) : Nat := (\d+)', SRC)}
QN = {v: n for n, v in Q.items()}


def act(q, a):
    if q >= len(TABLE):
        return None
    row = TABLE[q]
    code = row[a] if a < len(row) else 0
    if code == 0:
        return None
    x = code - 1
    return (x % 4, x // 4 % 2, x // 8)


def app(f, a):
    return a if f == 'id' else f


def sweep_ok(q, d, S, f, f2):
    return all(act(q, app(f, a)) == (app(f2, a), d, q) for a in S)


def sweep_fn(q, d, S, f):
    if sweep_ok(q, d, S, f, f):
        return f
    r = act(q, app(f, S[0] if S else 0))
    if r is not None and sweep_ok(q, d, S, f, r[0]):
        return r[0]
    return None


def view(lst):
    if not lst:
        return ('cell', 0, ())
    it = lst[0]
    if it[0] == 's':
        return ('cell', it[1], lst[1:])
    return ('block', it[1], it[2], lst[1:])


def mstep(sets, c):
    q, l, r, dl = c
    if q == BEEP:
        return None
    if not dl:
        v = view(r)
        if v[0] == 'cell':
            a, rest = v[1], v[2]
            x = act(q, a)
            if x is None:
                return None
            w, d, q2 = x
            return (q2, (('s', w),) + l, rest, False) if d == 1 else (q2, l, (('s', w),) + rest, True)
        i, f, rest = v[1], v[2], v[3]
        f2 = sweep_fn(q, 1, sets[i] if i < len(sets) else [], f)
        return None if f2 is None else (q, (('b', i, f2),) + l, rest, False)
    v = view(l)
    if v[0] == 'cell':
        a, rest = v[1], v[2]
        x = act(q, a)
        if x is None:
            return None
        w, d, q2 = x
        return (q2, (('s', w),) + rest, r, False) if d == 1 else (q2, rest, (('s', w),) + r, True)
    i, f, rest = v[1], v[2], v[3]
    f2 = sweep_fn(q, 0, sets[i] if i < len(sets) else [], f)
    return None if f2 is None else (q, rest, (('b', i, f2),) + r, True)


def run(sets, c, stop=None, limit=100000):
    """Run until stuck / beep / stop(c); returns (steps, c)."""
    for k in range(limit):
        if stop is not None and stop(c):
            return k, c
        c2 = mstep(sets, c)
        if c2 is None:
            return k, c
        c = c2
    raise RuntimeError('limit')


def reach(sets, c, t, limit=100000):
    for k in range(limit):
        if c == t:
            return k
        c = mstep(sets, c)
        if c is None:
            return None
    return None


def subst(c, fn):
    q, l, r, dl = c
    L = []
    for it in l:
        L += list(reversed(fn(it)))
    R = []
    for it in r:
        R += fn(it)
    return (q, tuple(L), tuple(R), dl)


def cons(i, b):
    return lambda it: [('s', app(it[2], b)), it] if it[0] == 'b' and it[1] == i else [it]


def snoc(i, b):
    return lambda it: [it, ('s', app(it[2], b))] if it[0] == 'b' and it[1] == i else [it]


# ---- pretty printing ----
def show_item(it):
    if it[0] == 's':
        return 'BM01'[it[1]]
    f = it[2]
    return 'v%d%s' % (it[1], '' if f == 'id' else '->' + 'BM01'[f])


def show(c):
    q, l, r, dl = c
    left = ' '.join(show_item(x) for x in reversed(l))
    right = ' '.join(show_item(x) for x in r)
    return '%s: %s %s %s' % (QN.get(q, q), left, '<' if dl else '>', right)


def lean_item(it):
    if it[0] == 's':
        return '.sym %d' % it[1]
    f = '.id' if it[2] == 'id' else '(.const %d)' % it[2]
    return '.blk %d %s' % (it[1], f)


def lean_sc(c):
    q, l, r, dl = c
    return '⟨%d, [%s], [%s], %s⟩' % (q, ', '.join(map(lean_item, l)), ', '.join(map(lean_item, r)),
                                    'true' if dl else 'false')


def sc(q, left, right, dl=False):
    """Build an SC from tape-order item lists: left in tape order."""
    if isinstance(q, str):
        q = Q[q]
    return (q, tuple(reversed(left)), tuple(right), dl)
