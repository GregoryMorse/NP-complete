"""Exact minimisation of a 2-symbol TM with don't-care transitions (SAT).

States p, q are compatible if they agree (write, move) wherever both are
defined, the beep state is never merged, and successors are compatible
(greatest fixed point).  A merge is an equivalence relation on states,
made of compatible pairs only, closed under successors.  We minimise the
number of classes with a MaxSAT / iterative cardinality search.
"""
import itertools
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver


def compat(t, beep):
    n = len(t)
    ns = len(t[0])

    def ok(p, q):
        if beep in (p, q):
            return False
        for s in range(ns):
            x, y = t[p][s], t[q][s]
            if x and y and (x[0] != y[0] or x[1] != y[1]):
                return False
        return True
    comp = {(p, q) for p in range(n) for q in range(p + 1, n) if ok(p, q)}
    changed = True
    while changed:
        changed = False
        for (p, q) in list(comp):
            for s in range(ns):
                x, y = t[p][s], t[q][s]
                if x and y:
                    a, c = sorted((x[2], y[2]))
                    if a != c and (a, c) not in comp:
                        comp.discard((p, q))
                        changed = True
                        break
    return comp


def minimize(t, beep, start=0, bound=None, verbose=True, solver='cadical153', budget=None, hint=None):
    n = len(t)
    ns = len(t[0])
    comp = compat(t, beep)
    pool = IDPool()
    def M(p, q):
        if p == q:
            return None
        a, c = (p, q) if p < q else (q, p)
        return pool.id(('m', a, c)) if (a, c) in comp else 0
    cl = []
    adj = {p: set() for p in range(n)}
    for (p, q) in comp:
        adj[p].add(q); adj[q].add(p)
    # transitivity over triangles among compatible pairs; forbid when third pair incompatible
    for p in range(n):
        for q in adj[p]:
            for r in adj[q]:
                if r == p or not (p < r):
                    continue
                mpq, mqr, mpr = M(p, q), M(q, r), M(p, r)
                if mpr == 0:
                    cl.append([-mpq, -mqr])
                else:
                    cl.append([-mpq, -mqr, mpr])
    # closure
    for (p, q) in comp:
        for s in range(ns):
            x, y = t[p][s], t[q][s]
            if x and y and x[2] != y[2]:
                cl.append([-M(p, q), M(x[2], y[2])])
    # leaders
    lead = []
    for p in range(n):
        L = pool.id(('L', p))
        lead.append(L)
        smaller = [M(q, p) for q in adj[p] if q < p]
        # L <-> not any smaller
        for v in smaller:
            cl.append([-L, -v])
        cl.append([L] + smaller)
    S = Solver(name=solver, bootstrap_with=cl)
    best = None
    hi = bound if bound is not None else n
    while True:
        card = CardEnc.atmost(lits=lead, bound=hi, vpool=pool, encoding=EncType.seqcounter)
        S2 = Solver(name=solver, bootstrap_with=cl + card.clauses)
        if hint is not None:
            ph = []
            for (p, q) in comp:
                v = pool.id(('m', p, q))
                ph.append(v if hint[p] == hint[q] else -v)
            for p in range(n):
                first = min(i for i in range(n) if hint[i] == hint[p])
                ph.append(lead[p] if first == p else -lead[p])
            S2.set_phases(ph)
        if budget:
            S2.conf_budget(budget)
            r = S2.solve_limited()
        else:
            r = S2.solve()
        if not r:
            break
        model = set(v for v in S2.get_model() if v > 0)
        k = sum(1 for L in lead if L in model)
        best = (k, model)
        if verbose:
            print('classes', k, flush=True)
        hi = k - 1
        S2.delete()
    k, model = best
    # build classes
    par = list(range(n))
    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]; x = par[x]
        return x
    for (p, q) in comp:
        if pool.id(('m', p, q)) in model:
            par[find(q)] = find(p)
    roots = sorted({find(i) for i in range(n)}, key=lambda r: (r != find(start), r))
    idx = {r: i for i, r in enumerate(roots)}
    out = [[None] * ns for _ in roots]
    for p in range(n):
        for s in range(ns):
            tr = t[p][s]
            if tr:
                v = (tr[0], tr[1], idx[find(tr[2])])
                o = out[idx[find(p)]]
                assert o[s] is None or o[s] == v
                o[s] = v
    return out, idx[find(beep)]
