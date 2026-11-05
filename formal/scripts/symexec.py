#!/usr/bin/env python3
"""Python mirror of formal/ZP/SymExec.lean, for designing segment checks.

Loads zpLogic from formal/ZP/Logic.lean.  Items: ('s', a) or ('b', i, f) with
f = 'id' or an int (constant).  SC = (q, l, r, dirL) with l nearest first.
"""
import os, re

HERE = os.path.dirname(os.path.abspath(__file__))
LOGIC = os.environ.get('LOGIC', 'Logic')   # e.g. LOGIC=LogicPP LOGICID=zpp
IDENT = os.environ.get('LOGICID', 'zp')
SRC = open(os.path.join(HERE, '..', 'ZP', LOGIC + '.lean')).read()


def _rows():
    rows = []
    for k in range(len(re.findall(r'def %sLogicRows\d+ ' % IDENT, SRC))):
        m = re.search(r'def %sLogicRows%d : List \(List Nat\) :=\s*\[(.*?)\]\n' % (IDENT, k), SRC, re.S)
        body = m.group(1)
        rows += [list(map(int, x.split(','))) for x in re.findall(r'\[([0-9, ]+)\]', body)]
    return rows


TABLE = _rows()
BEEP = int(re.search(r'def %sLogic : LTM := ⟨%sLogicRows, (\d+)⟩' % (IDENT, IDENT), SRC).group(1))
_BASE = open(os.path.join(HERE, '..', 'ZP', 'Logic.lean')).read()
Q = {n: int(v) for n, v in re.findall(r'def (\w+) : Nat := (\d+)', _BASE + SRC)}
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


def swap(i, f, rest):
    if rest and rest[0][0] == 's' and f == rest[0][1]:
        return (rest[0], ('b', i, f)) + tuple(rest[1:])
    return None


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
        if f2 is None:
            sw = swap(i, f, rest)
            return None if sw is None else (q, l, sw, False)
        return (q, (('b', i, f2),) + l, rest, False)
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
    if f2 is None:
        sw = swap(i, f, rest)
        return None if sw is None else (q, sw, r, True)
    return (q, rest, (('b', i, f2),) + r, True)


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


# ---- renaming, dropping empty variables, concrete steps ----
def ren(rho):
    def f(it):
        if it[0] == 's':
            return [it]
        ks = rho[it[1]] if it[1] < len(rho) else []
        return [('b', k, it[2]) for k in ks]
    return f


def trim(lst):
    lst = list(lst)
    while lst and (lst[-1] == ('s', 0) or (lst[-1][0] == 'b' and lst[-1][2] == 0)):
        lst.pop()
    return tuple(lst)


def ins(it, r):
    if it[0] == 'b' and it[2] != 'id' and r and r[0] == ('s', it[2]):
        return (r[0],) + ins(it, r[1:])
    return (it,) + tuple(r)


def canon(lst):
    out = ()
    for it in reversed(list(lst)):
        out = ins(it, out)
    return out


def norm(c, E):
    q, l, r, dl = c
    keep = lambda it: not (it[0] == 'b' and it[1] in E)
    return (q, trim(canon(filter(keep, l))), trim(canon(filter(keep, r))), dl)


def cstep(c):
    q, l, r, dl = c
    v = view(l if dl else r)
    if v[0] != 'cell':
        return None
    a, rest = v[1], v[2]
    x = act(q, a)
    if x is None:
        return None
    w, d, q2 = x
    if not dl:
        return (q2, (('s', w),) + l, rest, False) if d == 1 else (q2, l, (('s', w),) + rest, True)
    return (q2, (('s', w),) + rest, r, False) if d == 1 else (q2, rest, (('s', w),) + r, True)


def reachN(sets, E, c, t, limit=200000, first=False):
    """Fuel for mreachN (or mreach1N if first) from c to t, or None."""
    tn = norm(t, E)
    c = norm(c, E)
    k = 0
    if first:
        if c[0] == BEEP:
            return None
        c = cstep(c)
        k = 1
        if c is None:
            return None
    while k < limit:
        if norm(c, E) == tn:
            return k
        c = mstep(sets, c)
        if c is None:
            return None
        k += 1
    return None


def why(sets, c, n=10**6):
    """Run until stuck and show where."""
    k, c2 = run(sets, c, limit=n)
    return k, show(c2)


def comp(g, f):
    return f if g == 'id' else g


def mapF(g, it):
    if it[0] == 's':
        return ('s', app(g, it[1]))
    return ('b', it[1], comp(g, it[2]))


def inst(sigma):
    def f(it):
        if it[0] == 's':
            return [it]
        its = sigma[it[1]] if it[1] < len(sigma) else []
        return [mapF(it[2], x) for x in its]
    return f


def ops(c, os):
    """SC.ops: os = [(is_cons, var, sym)], applied innermost-last like the Lean."""
    for o in reversed(os):
        c = subst(c, cons(o[1], o[2]) if o[0] else snoc(o[1], o[2]))
    return c
