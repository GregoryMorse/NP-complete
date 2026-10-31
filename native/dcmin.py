"""Greedy minimisation of a TM with don't-care (undefined) transitions.

Merging two states is accepted only if the closure of the merge is
consistent: every symbol on which both members are defined must have the
same write and move, and the successors are merged too.  The merged machine
agrees with the original on every transition the original defines, so on
any run of the original that never meets an undefined transition the two
machines behave identically (same beeps, same tape).
"""


def merge_all(table, beep, start=0, rounds=3):
    n = len(table)
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
            for s in (0, 1):
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
        for i, a in enumerate(roots):
            if find(a) != a:
                continue
            for b in roots[i + 1:]:
                if find(b) != b or find(a) != a:
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
    return out, idx[find(beep)]
