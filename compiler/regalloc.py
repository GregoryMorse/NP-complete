"""Register coalescing for counter programs.

Must-zero analysis.  Z(t) = registers that are certainly 0 whenever control
is at instruction t (forward must-analysis, intersection at joins; the
nonzero edge of DEC r is infeasible when r is in Z).

Merge condition.  Registers a, b may share one physical register if every
instruction touching a has b in Z, and every instruction touching b has a in
Z.  Then  phys = a + b  is a simulation relation: INC/DEC on a (with b = 0)
behave identically on phys, including the zero test.  For a class C the
pairwise condition gives phys = sum(C).  Pinned registers are never merged
(they are decoded by the tests).
"""
import math
import random

import tm as TM
from cm import Program


def must_zero(prog):
    regs = prog.regs
    full = frozenset(regs)
    n = len(prog.code)
    Z = [None] * n               # None = unreached (top)
    Z[prog.entry] = full
    work = [prog.entry]
    while work:
        t = work.pop()
        z = Z[t]
        ins = prog.code[t]
        outs = []
        if ins[0] == 'INC':
            outs.append((ins[2], z - {ins[1]}))
        elif ins[0] == 'DEC':
            r = ins[1]
            if r not in z:
                outs.append((ins[2], z))
            outs.append((ins[3], z | {r}))
        else:
            outs.append((ins[1], z))
        for nxt, zz in outs:
            new = zz if Z[nxt] is None else (Z[nxt] & zz)
            if new != Z[nxt]:
                Z[nxt] = new
                work.append(nxt)
    return Z


def compat_matrix(prog):
    Z = must_zero(prog)
    regs = prog.regs
    touch = {r: [] for r in regs}
    for t, ins in enumerate(prog.code):
        if ins[0] in ('INC', 'DEC') and Z[t] is not None:
            touch[ins[1]].append(t)
    ok = {}
    for a in regs:
        for b in regs:
            if a < b:
                c = (all(b in Z[t] for t in touch[a]) and
                     all(a in Z[t] for t in touch[b]))
                ok[(a, b)] = ok[(b, a)] = c
    return ok


def rename(prog, mapping):
    code = []
    for ins in prog.code:
        if ins[0] in ('INC', 'DEC'):
            code.append((ins[0], mapping[ins[1]]) + tuple(ins[2:]))
        else:
            code.append(ins)
    return Program(code, prog.entry, prog.labels)


def allocate(prog, pinned=(), iters=30000, seed=1, restarts=3):
    """Anneal over (partition into compatible classes, class order).
    Returns (renamed_program, order, cost)."""
    rnd = random.Random(seed)
    ok = compat_matrix(prog)
    regs = list(prog.regs)
    pinned = set(pinned)

    def build(classes):
        mapping = {}
        names = []
        for cl in classes:
            name = next((r for r in cl if r in pinned), sorted(cl)[0])
            names.append(name)
            for r in cl:
                mapping[r] = name
        return mapping, names

    def cost(classes):
        mapping, names = build(classes)
        p2 = rename(prog, mapping)
        return TM.cost_estimate(p2, names), p2, names

    best = None
    for rs in range(restarts):
        # start: greedy first-fit merging in random order
        order = regs[:]
        rnd.shuffle(order)
        classes = []
        for r in order:
            for cl in classes:
                if r not in pinned and not (cl & pinned) and all(ok[(r, x)] for x in cl):
                    cl.add(r)
                    break
            else:
                classes.append({r})
        cur, _, _ = cost(classes)
        for it in range(iters):
            temp = 15.0 * (1 - it / iters) + 0.05
            cand = [set(c) for c in classes]
            mv = rnd.random()
            if mv < 0.4:                         # move a register to another class
                r = rnd.choice(regs)
                if r in pinned:
                    continue
                src = next(c for c in cand if r in c)
                j = rnd.randrange(len(cand) + 1)
                if j == len(cand):
                    if len(src) == 1:
                        continue
                    src.discard(r)
                    cand.insert(rnd.randrange(len(cand) + 1), {r})
                else:
                    dst = cand[j]
                    if dst is src or (dst & pinned) or not all(ok[(r, x)] for x in dst):
                        continue
                    src.discard(r)
                    dst.add(r)
                cand = [c for c in cand if c]
            elif mv < 0.7:                       # swap two classes
                i, j = rnd.randrange(len(cand)), rnd.randrange(len(cand))
                cand[i], cand[j] = cand[j], cand[i]
            else:                                # move a class
                i, j = rnd.randrange(len(cand)), rnd.randrange(len(cand))
                cand.insert(j, cand.pop(i))
            c, _, _ = cost(cand)
            if c <= cur or rnd.random() < math.exp((cur - c) / temp):
                classes, cur = cand, c
                if best is None or cur < best[0]:
                    best = (cur, [set(x) for x in classes])
    c, p2, names = cost(best[1])
    return p2, names, c, best[1]
