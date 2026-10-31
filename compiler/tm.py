"""Counter machine  ->  1-tape 2-symbol Turing machine.

Tape layout.  Register order o[0..k-1]; register o[i] with value v is the
block 1^(v+1); blocks are separated by a single 0; everything left of block 0
and right of the data is 0.  sep_i = the 0 right after block i;
E = sep_{k-1} is the canonical head position.

Every counter instruction t has an entry state ent[t] whose meaning is
"head on E, reading 0".  A transition taken while the head is on E having
just read 0 may instead *inline* the 0-transition of ent[t] (marker AT_E).

The single BEEP instruction owns the dedicated beep state, entered once per
beep and never merged with anything (progress obligation (c)).
"""
from collections import defaultdict

L, R = 'L', 'R'


class AtE:
    __slots__ = ('t',)

    def __init__(self, t):
        self.t = t

    def __repr__(self):
        return f'AtE({self.t})'


class Builder:
    def __init__(self):
        self.st = []            # list of [trans0, trans1]; trans=(w,m,next)|AtE|None
        self.names = []

    def new(self, name=''):
        self.st.append([None, None])
        self.names.append(name)
        return len(self.st) - 1

    def set(self, s, sym, tr):
        assert self.st[s][sym] is None, (s, sym)
        self.st[s][sym] = tr


def compile_cm(prog, order=None, inline=True, dec_mode='best'):
    """Return (table, info).  table[s] = [(w,m,n) or None, ...] with state 0
    the start state; info['beep'] = index of the beep state."""
    regs = list(order) if order else list(prog.regs)
    assert sorted(regs) == sorted(prog.regs)
    k = len(regs)
    pos = {r: i for i, r in enumerate(regs)}
    B = Builder()
    n = len(prog.code)
    ent = [B.new(f'ent{t}') for t in range(n)]
    beep_state = None

    def goto_at_E(t):
        """continuation when the head is on E having read 0."""
        return AtE(t) if inline else (0, R, _back_to_E_left(t))

    back_cache = {}

    def _back_to_E_left(t):
        # helper used only when inlining is off: we are on E (read 0);
        # step right onto E+1 (0) and come back.
        if t not in back_cache:
            s = B.new(f'back{t}')
            B.set(s, 0, (0, L, ent[t]))
            back_cache[t] = s
        return back_cache[t]

    zscan_cache = {}

    def zscan(t):
        """scan right from inside the data to E, then ent[t]."""
        if t not in zscan_cache:
            za, zb = B.new(f'za{t}'), B.new(f'zb{t}')
            B.set(za, 1, (1, R, za))
            B.set(za, 0, (0, R, zb))
            B.set(zb, 1, (1, R, za))
            B.set(zb, 0, (0, L, ent[t]))
            zscan_cache[t] = za
        return zscan_cache[t]

    def nav_left(t, m, op):
        """From ent[t] (on E) to sep at distance m blocks to the left;
        execute transition op there (on reading 0)."""
        if m == 0:
            B.set(ent[t], 0, op)
            return
        prev = ent[t]
        B.set(prev, 0, (0, L, None))
        for i in range(1, m + 1):
            s = B.new(f'nav{t}.{i}')
            w, mv, _ = B.st[prev][0]
            B.st[prev][0] = (w, mv, s)
            B.set(s, 1, (1, L, s))
            if i == m:
                B.set(s, 0, op)
            else:
                B.set(s, 0, (0, L, None))
            prev = s

    def shift_right_from_here(t_next, name):
        """Returns state C0: we have just written 1 over a 0 (carry 0) and
        moved right; shift the tail right by one and finish on E."""
        c0, c1 = B.new(name + 'c0'), B.new(name + 'c1')
        B.set(c0, 1, (0, R, c1))
        B.set(c0, 0, goto_at_E(t_next))
        B.set(c1, 1, (1, R, c1))
        B.set(c1, 0, (1, R, c0))
        return c0

    def emit_inc(t, r, nxt):
        m = k - 1 - pos[r]
        if m == 0:
            B.set(ent[t], 0, (1, R, ent[nxt]))
            return
        c0 = shift_right_from_here(nxt, f'inc{t}')
        nav_left(t, m, (1, R, c0))

    def emit_dec_last(t, nz, z):
        x, y, q = B.new(f'dl{t}x'), B.new(f'dl{t}y'), B.new(f'dl{t}q')
        B.set(ent[t], 0, (0, L, x))
        B.set(x, 1, (0, L, y))
        B.set(y, 1, (1, R, ent[nz]))
        B.set(y, 0, (0, R, q))
        B.set(q, 0, (1, R, ent[z]))

    def emit_dec_twopass(t, r, nz, z):
        m = k - 1 - pos[r]
        t1, t2, d1 = B.new(f'd{t}t1'), B.new(f'd{t}t2'), B.new(f'd{t}d1')
        y, z0, zz, w, u = (B.new(f'd{t}{c}') for c in ('y', 'z0', 'z', 'w', 'u'))
        nav_left(t, m, (0, L, t1))
        B.set(t1, 1, (1, L, t2))
        B.set(t2, 0, (0, R, zscan(z)))
        B.set(t2, 1, (1, R, d1))
        B.set(d1, 1, (0, R, y))
        B.set(y, 0, (1, R, z0))
        B.set(z0, 0, (0, L, u))
        B.set(z0, 1, (1, R, zz))
        B.set(zz, 1, (1, R, zz))
        B.set(zz, 0, (0, L, w))
        B.set(w, 1, (0, R, y))
        B.set(u, 1, (0, L, ent[nz]))

    def emit_dec_carry(t, r, nz, z):
        m = k - 1 - pos[r]
        # entry: step left onto last cell of block k-1 with carry 0
        k0 = B.new(f'dc{t}k0.0')
        B.set(ent[t], 0, (0, L, k0))
        for i in range(m):
            k1 = B.new(f'dc{t}k1.{i}')
            B.set(k0, 1, (0, L, k1))
            nk0 = B.new(f'dc{t}k0.{i+1}')
            B.set(k1, 1, (1, L, k1))
            B.set(k1, 0, (1, L, nk0))
            k0 = nk0
        kr, ua = B.new(f'dc{t}kr'), B.new(f'dc{t}ua')
        B.set(k0, 1, (0, L, kr))
        B.set(kr, 1, (1, R, zscan(nz)))
        B.set(kr, 0, (0, R, ua))
        c0 = shift_right_from_here(z, f'dc{t}')
        B.set(ua, 0, (1, R, c0))

    for t, ins in enumerate(prog.code):
        op = ins[0]
        if op == 'INC':
            emit_inc(t, ins[1], ins[2])
        elif op == 'DEC':
            _, r, nz, z = ins
            m = k - 1 - pos[r]
            if m == 0 and dec_mode == 'best':
                emit_dec_last(t, nz, z)
            elif dec_mode == 'carry' or (dec_mode == 'best' and 2 * m + 8 < m + 11):
                emit_dec_carry(t, r, nz, z)
            else:
                emit_dec_twopass(t, r, nz, z)
        elif op == 'BEEP':
            assert beep_state is None, 'one BEEP instruction only'
            beep_state = B.new('BEEP')
            B.set(ent[t], 0, (0, L, beep_state))
            B.set(beep_state, 1, (1, R, ent[ins[1]]))
        else:
            raise ValueError(op)

    # initialisation: write k empty blocks "1 0", finish on E -> ent[entry]
    start = B.new('start')
    cur = start
    for i in range(k):
        B.set(cur, 0, (1, R, None))
        if i == k - 1:
            w, mv, _ = B.st[cur][0]
            B.st[cur][0] = (w, mv, ent[prog.entry])
        else:
            s = B.new(f'init{i}')
            B.st[cur][0] = (1, R, s)
            nx = B.new(f'init{i}b')
            B.set(s, 0, (0, R, nx))
            cur = nx

    # resolve AtE markers
    def res(tr, depth=0):
        if isinstance(tr, AtE):
            assert depth < 3
            return res(B.st[ent[tr.t]][0], depth + 1)
        return tr
    for s in range(len(B.st)):
        for a in (0, 1):
            if B.st[s][a] is not None:
                B.st[s][a] = res(B.st[s][a])

    table, names, beep = _finish(B.st, B.names, start, beep_state)
    return table, {'beep': beep, 'names': names, 'order': regs, 'ent': None}


def _finish(st, names, start, beep):
    """Remove unreachable states; renumber with start = 0."""
    seen = {start}
    stack = [start]
    while stack:
        s = stack.pop()
        for tr in st[s]:
            if tr is not None and tr[2] not in seen:
                seen.add(tr[2])
                stack.append(tr[2])
    order = [start] + sorted(seen - {start})
    idx = {s: i for i, s in enumerate(order)}
    table = []
    for s in order:
        table.append([None if tr is None else (tr[0], tr[1], idx[tr[2]]) for tr in st[s]])
    return table, [names[s] for s in order], idx.get(beep)


def minimize(table, beep, start=0):
    """Merge bisimilar states (Moore partition refinement).  The beep state
    is kept in a singleton class.  Undefined transitions are treated as a
    distinct 'undefined' value (so merging never invents behaviour)."""
    n = len(table)
    cls = [0] * n
    if beep is not None:
        cls[beep] = 1
    while True:
        sig = {}
        new = [0] * n
        for s in range(n):
            key = (cls[s], s == beep,
                   tuple(None if tr is None else (tr[0], tr[1], cls[tr[2]]) for tr in table[s]))
            if s == beep:
                key = ('BEEP',)
            new[s] = sig.setdefault(key, len(sig))
        if len(sig) == len(set(cls)):
            cls = new
            break
        cls = new
    # build quotient
    rep = {}
    for s in range(n):
        rep.setdefault(cls[s], s)
    order = [cls[start]] + sorted(set(cls) - {cls[start]}, key=lambda c: rep[c])
    idx = {c: i for i, c in enumerate(order)}
    out = []
    for c in order:
        s = rep[c]
        out.append([None if tr is None else (tr[0], tr[1], idx[cls[tr[2]]]) for tr in table[s]])
    return out, (idx[cls[beep]] if beep is not None else None)


def cost_estimate(prog, order):
    """Static state count estimate for a register order (before sharing)."""
    k = len(order)
    pos = {r: i for i, r in enumerate(order)}
    c = 2 * k
    for ins in prog.code:
        if ins[0] == 'INC':
            m = k - 1 - pos[ins[1]]
            c += 1 if m == 0 else m + 3
        elif ins[0] == 'DEC':
            m = k - 1 - pos[ins[1]]
            c += 4 if m == 0 else min(2 * m + 8, m + 11)
        else:
            c += 2
    return c


def optimize_order(prog, iters=20000, seed=1):
    import random
    rnd = random.Random(seed)
    # initial: by frequency, hottest last
    freq = defaultdict(int)
    for ins in prog.code:
        if ins[0] in ('INC', 'DEC'):
            freq[ins[1]] += 1
    order = sorted(prog.regs, key=lambda r: freq[r])
    best = cost_estimate(prog, order)
    for _ in range(iters):
        i, j = rnd.randrange(len(order)), rnd.randrange(len(order))
        if i == j:
            continue
        order[i], order[j] = order[j], order[i]
        c = cost_estimate(prog, order)
        if c <= best:
            best = c
        else:
            order[i], order[j] = order[j], order[i]
    return order, best


# ------------------------------------------------------------ formats
def letters(i):
    return str(i)


def to_standard(table):
    """bbchallenge-style text: states separated by '_', each state is two
    transitions 'wMn' with n a state *number* (states > 26 need numbers);
    '---' marks an undefined transition."""
    parts = []
    for s in table:
        p = []
        for tr in s:
            p.append('---' if tr is None else f'{tr[0]}{tr[1]}{tr[2]}')
        parts.append(','.join(p))
    return '_'.join(parts)


def to_letters(table):
    """Standard bbchallenge format (valid only if <= 26 states...) - for
    larger machines we use base-26 multi-letter state names separated by
    nothing would be ambiguous, so this is only used for small machines."""
    A = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'
    assert len(table) <= 26
    return '_'.join(''.join('---' if tr is None else f'{tr[0]}{tr[1]}{A[tr[2]]}' for tr in s)
                    for s in table)


# ------------------------------------------------------------ simulator
def simulate(table, steps, beep=None, on_beep=None, tape=None):
    """Plain Python simulator (for tests).  Returns (steps_done, state,
    head, tape dict)."""
    tape = tape if tape is not None else defaultdict(int)
    s, h = 0, 0
    for i in range(steps):
        tr = table[s][tape[h]]
        if tr is None:
            return i, s, h, tape, 'halt'
        tape[h] = tr[0]
        h += 1 if tr[1] == 'R' else -1
        s = tr[2]
        if s == beep and on_beep is not None:
            if on_beep(i + 1, tape, h) is False:
                return i + 1, s, h, tape, 'stop'
    return steps, s, h, tape, 'limit'


def decode_regs(tape, h, order, at_E=True):
    """Decode register values from a tape where the head is on E (or, for
    the beep state, on the last data cell: pass at_E=False)."""
    pos = h if at_E else h + 1
    vals = []
    p = pos - 1
    for _ in range(len(order)):
        c = 0
        while tape.get(p, 0) == 1:
            c += 1
            p -= 1
        vals.append(c - 1)
        p -= 1
    vals.reverse()
    return dict(zip(order, vals))
