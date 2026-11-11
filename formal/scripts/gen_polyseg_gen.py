"""Generate Lean segment lemmas for zppolyLogic from the Python symbolic executor.

seg(name, doc, vars, start, stop, cases=None, hyp_names=None)
  vars: ordered dict  name -> set key   (bits, NB, ALL, O13, T3, Z2)
  start: (state, left_tokens, right_tokens, dl)   left in tape order
  tokens: int symbol | 'X' variable block | ('X', c) block of constant c | '@b' single bit variable
  stop: state name (first time reached) or (state, occurrence)
"""
import os, sys
os.environ['LOGIC'] = 'LogicPoly'
os.environ['LOGICID'] = 'zppoly'
sys.path.insert(0, '/home/user/np-complete/.claude/worktrees/agent-a63be367c1b1600e3/formal/scripts')
import symexec as S

SETS = {'bits': [2, 3], 'NB': [1, 2, 3], 'ALL': [0, 1, 2, 3], 'O13': [1, 3], 'T3': [3], 'Z2': [2]}
HYP = {'bits': 'Bits', 'NB': 'NoB', 'ALL': 'Sym4'}


def qname(q):
    n = S.QN[q]
    return ('QPoly.' if q >= 129 else 'Q.') + n


def items(vs, toks, subst=None):
    out = []
    for t in toks:
        if isinstance(t, int):
            out.append(('s', t))
        elif isinstance(t, tuple):
            out.append(('b', vs.index(t[0]), t[1]))
        elif t.startswith('@'):
            out.append(('s', subst[t]))
        else:
            out.append(('b', vs.index(t), 'id'))
    return tuple(out)


def lean_expr(vs, its):
    # its: tape-order items
    def one(it):
        if it[0] == 's':
            return ('sym', str(it[1]))
        v = vs[it[1]]
        if it[2] == 'id':
            return ('blk', v)
        return ('blk', 'List.replicate %s.length %d' % (v, it[2]))
    parts = [one(i) for i in its]
    if not parts:
        return '[]'
    s = None
    for p in reversed(parts):
        if s is None:
            s = '[%s]' % p[1] if p[0] == 'sym' else p[1]
        else:
            s = '%s :: (%s)' % (p[1], s) if p[0] == 'sym' else '%s ++ (%s)' % (p[1], s)
    return s


def lean_items(its):
    return '[%s]' % ', '.join(S.lean_item(i) for i in its)


def tape_order_left(c):
    return tuple(reversed(c[1]))


def run_one(vs, vsets, start, stop, subst):
    q, lt, rt, dl = start
    c = S.sc(q, items(vs, lt, subst), items(vs, rt, subst), dl)
    sets = [SETS[vsets[v]] for v in vs]
    sname, occ = (stop, 1) if isinstance(stop, str) else stop
    qs = S.Q[sname]
    cur = c
    seen = 0
    for k in range(200000):
        if cur[0] == qs and k > 0:
            seen += 1
            if seen == occ:
                break
        n = S.mstep(sets, cur)
        if n is None:
            raise RuntimeError('stuck at %s after %d: %s' % (sname, k, S.show(cur)))
        cur = n
    k = S.reachN(sets, [], c, cur)
    cur = (cur[0], S.trim(cur[1]), S.trim(cur[2]), cur[3])
    return c, cur, k


def seg(name, doc, vsets, start, stop, cases=None, extra_hyps=''):
    vs = list(vsets)
    cases = cases or {}
    # case enumeration
    keys = list(cases)
    combos = [dict()]
    for kk in keys:
        combos = [dict(c, **{kk: v}) for c in combos for v in cases[kk]]
    res = []
    for sub in combos:
        res.append((sub,) + run_one(vs, vsets, start, stop, sub))
    # statement from the first (symbolic) description: use variable names for case symbols
    q, lt, rt, dl = start
    c0, cend0 = res[0][1], res[0][2]
    # end tokens: rebuild by variable naming: use first combo's end config, but the case symbols
    # appear as numerals there; map back for statement by recomputing with placeholder symbol 9?
    # Simplest: write the statement from the start tokens with names, end from combo 0 and
    # replace numerals by the case variable only when unique -- instead we re-run with sentinel values.
    sent = {k: 5 + i for i, k in enumerate(keys)}  # sentinel symbols not in the 4-symbol alphabet
    stmt_end = None
    if keys:
        # run with real values, then substitute: find the positions where the real value of case var
        # is the only difference between combos
        endsets = []
        for sub, c, ce, k in res:
            endsets.append((sub, tape_order_left(ce), ce[2], ce[3]))
        base = endsets[0]
        end_l = list(base[1])
        end_r = list(base[2])

        def gen_syms(i):
            # decide for each sym position whether it equals the case var in all combos
            return None
        # build end item lists per combo and compare position-wise
        def unify(pos_lists):
            out = []
            for items_at in zip(*pos_lists):
                if all(x == items_at[0] for x in items_at):
                    out.append(items_at[0])
                else:
                    # differs: must be a case symbol
                    for kk in keys:
                        if all(it == ('s', res[j][0][kk]) for j, it in enumerate(items_at)):
                            out.append(('v', kk))
                            break
                    else:
                        raise RuntimeError('cannot unify %r' % (items_at,))
            return out
        ll = [e[1] for e in endsets]
        rr = [list(e[2]) for e in endsets]
        assert len({len(x) for x in ll}) == 1 and len({len(x) for x in rr}) == 1
        end_l = unify(ll)
        end_r = unify(rr)
        end_dl = base[3]
    else:
        ce = cend0
        end_l = list(tape_order_left(ce))
        end_r = list(ce[2])
        end_dl = ce[3]

    def expr(its):
        out = []
        for it in its:
            if it[0] == 'v':
                out.append(('sym', it[1][1:]))
            elif it[0] == 's':
                out.append(('sym', str(it[1])))
            else:
                v = vs[it[1]]
                out.append(('blk', v if it[2] == 'id' else 'List.replicate %s.length %d' % (v, it[2])))
        if not out:
            return '[]'
        s = None
        for p in reversed(out):
            if s is None:
                s = '[%s]' % p[1] if p[0] == 'sym' else p[1]
            else:
                s = '%s :: (%s)' % (p[1], s) if p[0] == 'sym' else '%s ++ (%s)' % (p[1], s)
        return s

    def litems(its):
        out = []
        for it in its:
            if it[0] == 'v':
                out.append('.sym %s' % it[1][1:])
            else:
                out.append(S.lean_item(it))
        return '[%s]' % ', '.join(out)

    st_l = items(vs, lt, {k: 0 for k in keys})  # placeholders not used
    # start item lists with symbol names for the case vars
    def start_items(toks):
        out = []
        for t in toks:
            if isinstance(t, int):
                out.append(('s', t))
            elif isinstance(t, tuple):
                out.append(('b', vs.index(t[0]), t[1]))
            elif t.startswith('@'):
                out.append(('v', t))
            else:
                out.append(('b', vs.index(t), 'id'))
        return out
    sl, sr = start_items(lt), start_items(rt)
    flag = ('T' if dl else 'F') + ('T' if end_dl else 'F')
    qs = S.Q[start[0]]
    qe = [x for x in [S.QN[res[0][2][0]]]][0]
    qe_id = res[0][2][0]
    hn = lambda v: 'h' + v
    sig = ' '.join('(%s : List Nat)' % v for v in vs if True)
    sig += ''.join(' (%s : Nat)' % k[1:] for k in keys)
    hyps = ''
    for v in vs:
        s = vsets[v]
        if s in HYP:
            hyps += ' (h%s : %s %s)' % (v, HYP[s], v)
        else:
            hyps += ' (h%s : ∀ a ∈ %s, a ∈ %s)' % (v, v, s)
    for k in keys:
        hyps += ' (h%s : %s ∈ %s)' % (k[1:], k[1:], 'bits' if cases[k] == [2, 3] else 'NB')
    hyps += extra_hyps
    reach = 'zppolyLogic.Reach (%s %s (%s) (%s)) (%s %s (%s) (%s))' % (
        'hd' if dl else 'hdR', qname(start[0]) if False else qname(S.Q[start[0]]), expr(sl), expr(sr),
        'hd' if end_dl else 'hdR', qname(qe_id), expr(end_l), expr(end_r))
    setlist = ', '.join(vsets[v] for v in vs)
    valid = 'Valid [%s] [%s]' % (setlist, ', '.join(vs))
    vcons = '(Valid.nil _)'
    for v in reversed(vs):
        vcons = '(Valid.cons h%s %s)' % (v, vcons)
    vcons = vcons[1:-1] if vcons.startswith('(') else vcons
    body = []
    def check(k, sub, cs):
        c, ce, kk = cs
        return ('exact check%s (env := [%s]) (E := []) (k := %d) hV trivial\n'
                '      (ls := %s) (rs := %s)\n      (ls\' := %s) (rs\' := %s)\n'
                '      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)') % (
            flag, ', '.join(vs), kk, litems(sl_sub(sub)), litems(sr_sub(sub)), litems(end_l_sub(sub)), litems(end_r_sub(sub)))

    def subst_items(its, sub):
        out = []
        for it in its:
            if it[0] == 'v':
                out.append(('s', sub[it[1]]))
            else:
                out.append(it)
        return out
    sl_sub = lambda sub: subst_items(sl, sub)
    sr_sub = lambda sub: subst_items(sr, sub)
    end_l_sub = lambda sub: subst_items(end_l, sub)
    end_r_sub = lambda sub: subst_items(end_r, sub)
    txt = '/-- %s -/\ntheorem %s %s%s :\n    %s := by\n' % (doc, name, sig, hyps, reach)
    txt += '  have hV : %s := %s\n' % (valid, vcons)
    if not keys:
        txt += '  ' + check(0, {}, res[0][1:]).replace('\n', '\n  ') + '\n'
    else:
        rc = []
        for kk in keys:
            vals = cases[kk]
            if vals == [2, 3]:
                rc.append('rcases mem_bits h%s with rfl | rfl' % kk[1:])
            elif vals == [1, 2, 3]:
                rc.append('rcases (show %s = 1 ∨ %s = 2 ∨ %s = 3 by simpa [NB] using h%s) with rfl | rfl | rfl' % (kk[1:], kk[1:], kk[1:], kk[1:]))
            else:
                raise RuntimeError('unknown case set')
        txt += '  ' + ' <;> '.join(rc) + '\n'
        for sub, c, ce, k in res:
            txt += '  · ' + check(0, sub, (c, ce, k)).replace('\n', '\n    ') + '\n'
    return txt, [r[3] for r in res]
