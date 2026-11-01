"""Reads that are impossible given the symbol the previous step wrote:
explore (state, known read, ctx) where ctx = (side, symbol) of the pair just
left; prune transitions into copies that can read nothing; report states
whose reachable reads are a strict subset of their defined reads."""
import zp2

def analyse(m):
    start = (m.start, None, None)
    d2 = {}
    seen = {start}; work = [start]
    while work:
        st = work.pop(); q, kr, ctx = st
        for a in 'BM01':
            if kr is not None and a != kr: continue
            tr = m.d.get((q, a))
            if tr is None: continue
            w, d, n = tr
            nkr = ctx[1] if (ctx is not None and ctx[0] == d) else None
            nst = (n, nkr, ('L' if d == 'R' else 'R', w))
            d2[(st, a)] = nst
            if nst not in seen: seen.add(nst); work.append(nst)
    while True:
        alive = {s for (s, a) in d2}
        dead = [k for k, v in d2.items() if v not in alive]
        if not dead: break
        for k in dead: del d2[k]
    # reachable from start again
    reach = {start}; work = [start]
    while work:
        s = work.pop()
        for a in 'BM01':
            n = d2.get((s, a))
            if n is not None and n not in reach: reach.add(n); work.append(n)
    reads = {}
    for (s, a) in d2:
        if s in reach: reads.setdefault(s[0], set()).add(a)
    out = {}
    for q in m.states():
        dfd = {a for a in 'BM01' if (q, a) in m.d}
        r = reads.get(q, set())
        if r != dfd: out[q] = (sorted(dfd - r))
    return out

if __name__ == '__main__':
    print(analyse(zp2.build()))
