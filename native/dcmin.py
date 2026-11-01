"""Greedy minimisation of a TM with don't-care (undefined) transitions.

Merging two states is accepted only if the closure of the merge is
consistent: every symbol on which both members are defined must have the
same write and move, and the successors are merged too.  The merged machine
agrees with the original on every transition the original defines, so on
any run of the original that never meets an undefined transition the two
machines behave identically (same beeps, same tape).
"""


def merge_all(table, beep, start=0, rounds=3, order=None, allowed=None, ret_map=False):
    n = len(table)
    nsym = len(table[0])
    par = list(range(n))
    trans = [list(r) for r in table]

    def find(x):
        while par[x] != x:      # no path compression: merges may be rolled back
            x = par[x]
        return x

    def try_merge(a, b):
        saved_par = {}
        saved_tr = {}
        stack = [(a, b)]
        while stack:
            x, y = stack.pop()
            x, y = find(x), find(y)
            if x == y:
                continue
            if beep in (x, y) or (find(beep) in (x, y)):
                break
            ok = True
            new = []
            for s in range(nsym):
                tx, ty = trans[x][s], trans[y][s]
                if tx is None:
                    new.append(ty)
                elif ty is None:
                    new.append(tx)
                elif tx[0] != ty[0] or tx[1] != ty[1]:
                    ok = False
                    break
                else:
                    new.append(tx)
                    stack.append((tx[2], ty[2]))
            if not ok:
                break
            if x == find(start):
                x, y = y, x
            # merge x into y (keep start as a root)
            saved_par.setdefault(x, par[x])
            saved_tr.setdefault(y, list(trans[y]))
            par[x] = y
            trans[y] = new
        else:
            return True
        for k, v in saved_par.items():
            par[k] = v
        for k, v in saved_tr.items():
            trans[k] = v
        return False

    for _ in range(rounds):
        changed = False
        roots = [i for i in range(n) if find(i) == i]
        if order is not None:
            roots = order(roots)
        for i, a in enumerate(roots):
            if find(a) != a:
                continue
            for b in roots[i + 1:]:
                if find(b) != b or find(a) != a:
                    continue
                if allowed is not None and not allowed(a, b):
                    continue
                if try_merge(a, b):
                    changed = True
        if not changed:
            break
    roots = sorted({find(i) for i in range(n)}, key=lambda r: (r != find(start), r))
    idx = {r: k for k, r in enumerate(roots)}
    out = []
    for r in roots:
        out.append([None if tr is None else (tr[0], tr[1], idx[find(tr[2])]) for tr in trans[r]])
    if ret_map:
        return out, idx[find(beep)], [idx[find(i)] for i in range(n)]
    return out, idx[find(beep)]


def merge_logical(m, **kw):
    """Apply merge_all to a logical machine (symbols B M 0 1)."""
    from logic import LTM, SYMS
    qs = m.states()
    ix = {q: i for i, q in enumerate(qs)}
    table = [[None if (q, a) not in m.d else
              (m.d[(q, a)][0], m.d[(q, a)][1], ix[m.d[(q, a)][2]]) for a in SYMS] for q in qs]
    out, b = merge_all(table, ix[m.beep], **kw)
    names = ['S%d' % i for i in range(len(out))]
    m2 = LTM(names[0])
    for i, row in enumerate(out):
        for a, tr in zip(SYMS, row):
            if tr is not None:
                m2.t(names[i], a, tr[0], tr[1], names[tr[2]])
    m2.beep = names[b]
    return m2
