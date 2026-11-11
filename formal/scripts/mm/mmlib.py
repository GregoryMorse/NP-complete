import os, sys, itertools
os.environ['MACH'] = 'MM'
os.environ['IDN'] = 'zmm'
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_lib as G
S = G.S
G.KIND.update({'B0': [0], 'bits1': [1, 2, 3], 'M1': [1], 'B01': [0, 2, 3], 'BM': [0, 1]})
G.HYP.update({'B0': '(h{n} : ∀ a ∈ {n}, a ∈ B0)', 'M1': '(h{n} : ∀ a ∈ {n}, a ∈ M1s)', 'B01': '(h{n} : ∀ a ∈ {n}, a ∈ B01)'})
G.SETN.update({'B0': 'B0', 'M1': 'M1s', 'B01': 'B01'})
KIND, HYP, SETN = G.KIND, G.HYP, G.SETN
qn = G.qn


def expr(items, names):
    acc = '[]'
    for it in reversed(items):
        if it[0] in ('s', 'p', 't'):
            v = str(it[1]) if it[0] != 't' else it[1]
            acc = '[%s]' % v if acc == '[]' else '%s :: (%s)' % (v, acc)
        else:
            x = names[it[1]]
            if it[2] != 'id':
                x = 'List.replicate %s.length %d' % (x, it[2])
            acc = x if acc == '[]' else '%s ++ (%s)' % (x, acc)
    return acc


def lit(items, sub=None):
    o = []
    for it in items:
        if it[0] == 's':
            o.append('.sym %d' % it[1])
        elif it[0] == 'p':
            o.append('.sym %d' % sub[it[1]])
        elif it[0] == 't':
            o.append('.sym %d' % it[2](sub))
        else:
            o.append('.blk %d %s' % (it[1], '.id' if it[2] == 'id' else '(.const %d)' % it[2]))
    return '[' + ', '.join(o) + ']'


def conc(items, sub):
    out = []
    for it in items:
        if it[0] == 'p':
            out.append(('s', sub[it[1]]))
        elif it[0] == 't':
            out.append(('s', it[2](sub)))
        else:
            out.append(it)
    return out

B_, M_, Z_, O_ = 0, 1, 2, 3   # blank, M, '0', '1'
DOM = {'bits': [2, 3], 'bm': [1, 0]}
DHYP = {'bits': '(h{q} : {q} ∈ bits)', 'bm': '(h{q} : {q} = 1 ∨ {q} = 0)'}
DRC = {'bits': 'rcases mem_bits h{q} with rfl | rfl', 'bm': 'rcases h{q} with rfl | rfl'}

OUT = []


def theorem(name, doc, vars_, params, start, end, tt='FF'):
    """params: list of (name, domain)."""
    names = [v for v, _ in vars_]
    kinds = [k for _, k in vars_]
    sets = [KIND[k] for k in kinds]
    pn = [q for q, _ in params]
    binders = ' '.join('(%s : List Nat)' % v for v in names) + ''.join(' (%s : Nat)' % q for q in pn)
    hyps = ' '.join(HYP[k].format(n=n) for n, k in vars_) + ''.join(' ' + DHYP[d].format(q=q) for q, d in params)

    def stm(t, dl):
        q, l, r = t
        return '%s %s (%s) (%s)' % ('hd' if dl else 'hdR', qn(q), expr(l, names), expr(r, names))
    sdl = tt[0] == 'T'
    edl = tt[1] == 'T'
    head = '/-- %s -/\ntheorem %s %s %s :\n    zmmLogic.Reach (%s)\n      (%s) := by\n' % (doc, name, binders, hyps, stm(start, sdl), stm(end, edl))
    valid = 'Valid [%s] [%s] := %s' % (', '.join(SETN[k] for k in kinds), ', '.join(names),
                                      ''.join('Valid.cons h%s (' % n for n in names) + 'Valid.nil _' + ')' * len(names))
    head += '  have hV : %s\n' % valid
    envs = '[%s]' % ', '.join(names)
    bad = []

    def one(sub, indent):
        k = S.reachN(sets, [], S.sc(start[0], conc(start[1], sub), conc(start[2], sub), sdl), S.sc(end[0], conc(end[1], sub), conc(end[2], sub), edl))
        if k is None:
            c0 = S.sc(start[0], conc(start[1], sub), conc(start[2], sub), sdl)
            print('NO PATH', name, sub, S.show(S.run(sets, c0, limit=100000)[1]), file=sys.stderr)
            k = -1
            bad.append(name)
        return ('%sexact check%s (env := %s) (E := []) (k := %d) hV trivial\n%s  (ls := %s) (rs := %s)\n%s  (ls\' := %s) (rs\' := %s)\n%s  (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)\n'
                % (indent, tt, envs, k, indent, lit(start[1], sub), lit(start[2], sub), indent, lit(end[1], sub), lit(end[2], sub), indent))
    if not params:
        body = one({}, '  ')
    else:
        rc = ' <;> '.join(DRC[d].format(q=q) for q, d in params)
        body = '  %s\n' % rc
        for sub in itertools.product(*[DOM[d] for _, d in params]):
            sd = dict(zip(pn, sub))
            body += '  · ' + one(sd, '    ').lstrip()
    return head + body + '\n'


def conv(items, names, pn):
    out = []
    for it in items:
        if isinstance(it, int):
            out.append(('s', it))
        elif isinstance(it, str):
            if it.startswith('@'):
                out.append(('p', it[1:]))
            else:
                out.append(('b', names.index(it), 'id'))
        elif it[0] == 'c':
            out.append(('b', names.index(it[1]), it[2]))
        elif it[0] == 'f':
            out.append(('t', it[1], it[2]))
        else:
            raise ValueError(it)
    return out


def rev(l):
    return list(reversed(l))


def cfg(q, dl, head, dr):
    """display notation: items left of the head, the head cell, items right of the head (display order).
    Returns (state, Lean-left, Lean-right) for hdR."""
    return (q, rev(dr), [head] + rev(dl))


def back(it, names):
    if it[0] == 's':
        return it[1]
    if it[2] == 'id':
        return names[it[1]]
    return ('c', names[it[1]], it[2])


def autoend(vars_, st, target, tt_end='F'):
    """Run the executor from st (internal items) until state `target`; return end (state, left, right) in spec items."""
    names = [v for v, _ in vars_]
    sets = [KIND[k] for k, _ in [(k, 0) for _, k in vars_]]
    c = S.sc(st[0], conc(st[1], {}), conc(st[2], {}), False)
    c = S.norm(c, [])
    for _ in range(100000):
        if c[0] == S.Q[target]:
            break
        c = S.mstep(sets, c)
        if c is None:
            raise RuntimeError('autoend: stuck before %s' % target)
    q, l, r, dl = c
    l = list(l)
    r = list(r)
    if dl:
        assert l[0][0] == 's', 'head on a block cell'
        r = [l[0]] + r
        l = l[1:]
    return (target, [back(x, names) for x in reversed(l)], [back(x, names) for x in r])


def spec(name, doc, vars_, start, end, params=(), tt='FF'):
    names = [v for v, _ in vars_]
    pn = [q for q, _ in params]
    st = (start[0], conv(start[1], names, pn), conv(start[2], names, pn))
    if isinstance(end, str):
        end = autoend(vars_, st, end)
    en = (end[0], conv(end[1], names, pn), conv(end[2], names, pn))
    txt = theorem(name, doc, vars_, list(params), st, en, tt)
    OUT.append(txt)
    return txt
