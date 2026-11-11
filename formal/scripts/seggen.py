#!/usr/bin/env python3
"""Generate Lean segment lemmas (`checkTT`/`checkTF`/`checkFT`/`checkFF` calls of ZP/SymExec.lean) from a
compact description, finding the fuel `k` with the Python mirror scripts/symexec.py.

Usage (as a library; see formal/scripts/gen_mh*.py):

    import seggen
    g = seggen.Gen(machine='mhBase', rows='mhBase', logic='LogicBaseMH', qfiles=['LogicBaseMH'],
                   ns={'Q': ..., })
    print(g.theorem(name='segX', doc='...', binders='(Qw : List Nat) ...', hyps=..., ...))

A *variable* is a word that the segment treats as a block: kind 'list' (items `.blk i .id`, symbol set
`bits`, `ALL` or `NB`), 'zeros' (`List.replicate g 0`, items `.blk i (.const 0)`), 'ones', or 'empty'
(`[]`, omitted from the items).  Tape items are given as strings of space separated tokens:

    B M 0 1        the symbols (B = 0, M = 1, '0' = 2, '1' = 3)
    $x             a symbol parameter `x` (a Lean `Nat` variable, case split by `cases`)
    name           a block variable
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SYM = {'B': 0, 'M': 1, '0': 2, '1': 3}
SETS = {'bits': [2, 3], 'ALL': [0, 1, 2, 3], 'NB': [1, 2, 3]}
HYP = {'bits': 'Bits', 'ALL': 'Sym4', 'NB': 'NoB'}


class Var:
    def __init__(self, name, kind='list', sset='bits', expr=None, hyp=None):
        self.name, self.kind, self.sset = name, kind, sset
        self.expr = expr or {'list': name, 'zeros': 'List.replicate %s 0' % name,
                             'ones': 'List.replicate %s 1' % name, 'empty': '[]'}[kind]
        if kind == 'zeros':
            self.sset = 'ALL'
        if kind == 'ones':
            self.sset = 'ALL'
        self.hyp = hyp or {'list': 'h' + name, 'zeros': 'zeros4 %s' % name, 'ones': 'ones4 %s' % name,
                           'empty': 'Bits.nil'}[kind]


def load_machine(logic, rows, qfiles):
    """Import scripts/symexec.py configured for the given Lean row definitions."""
    os.environ['LOGIC'] = logic
    os.environ['ROWS'] = rows
    os.environ['QFILES'] = ','.join(qfiles)
    os.environ.setdefault('LOGICID', 'zp')
    sys.path.insert(0, HERE)
    for m in ('symexec',):
        sys.modules.pop(m, None)
    import symexec
    return symexec


class Gen:
    def __init__(self, machine, rows, logic, qfiles=(), nsmap=None):
        self.machine = machine
        self.sx = load_machine(logic, rows, list(qfiles))
        # state name -> Lean name
        self.nsmap = {}
        for fn, ns in (nsmap or {}).items():
            src = open(os.path.join(HERE, '..', 'ZP', fn + '.lean')).read()
            for n in re.findall(r'def (\w+) : Nat := \d+', src):
                self.nsmap.setdefault(n, ns)
        base = open(os.path.join(HERE, '..', 'ZP', 'Logic.lean')).read()
        for n in re.findall(r'def (\w+) : Nat := \d+', base):
            self.nsmap.setdefault(n, 'Q')

    def qn(self, name):
        return '%s.%s' % (self.nsmap.get(name, 'Q'), name)

    # ---- items ----
    def items(self, toks, vars_, sub):
        """tokens -> list of python symexec items; sub maps $x to a number."""
        out = []
        idx = {v.name: i for i, v in enumerate(vars_)}
        for t in toks.split():
            if t in SYM:
                out.append(('s', SYM[t]))
            elif t.startswith('$'):
                out.append(('s', sub[t[1:]]))
            elif t in idx:
                v = vars_[idx[t]]
                if v.kind == 'empty':
                    continue
                f = 'id' if v.kind == 'list' else (0 if v.kind == 'zeros' else 1)
                out.append(('b', idx[t], f))
            else:
                raise KeyError(t)
        return out

    def lean_items(self, its):
        def one(it):
            if it[0] == 's':
                return '.sym %d' % it[1]
            return '.blk %d %s' % (it[1], '.id' if it[2] == 'id' else '(.const %d)' % it[2])
        return '[' + ', '.join(one(i) for i in its) + ']'

    def expr(self, toks, vars_, params):
        """Lean list expression for the tokens; `params` maps $x to the text used (variable name or number)."""
        parts, run = [], []
        idx = {v.name: v for v in vars_}

        def flush():
            if run:
                parts.append('[' + ', '.join(run) + ']')
                run.clear()
        for t in toks.split():
            if t in SYM:
                run.append(str(SYM[t]))
            elif t.startswith('$'):
                run.append(str(params[t[1:]]))
            else:
                v = idx[t]
                if v.kind == 'empty':
                    continue
                flush()
                parts.append(v.expr)
        flush()
        return ' ++ '.join(parts) if parts else '[]'

    def fuel(self, sets, q, ls, rs, dl, q2, ls2, rs2, dl2, empty_idx=()):
        sx = self.sx
        c = sx.sc(q, ls, rs, dl)
        t = sx.sc(q2, ls2, rs2, dl2)
        return sx.reachN(sets, list(empty_idx), c, t)

    def theorem(self, name, doc, binders, vars_, start, end, cases=(), pre='', derived=None, maxk=20000):
        """start/end = (state, dirL, leftToks, rightToks).  cases: list of (param, [values], hyp) split by
        rcases; the values 2/3 use `mem_bits` and values 0/2/3 use the hypothesis `hyp` as a disjunction.
        params of cases appear as `$param` in the item strings."""
        sx = self.sx
        sets = [SETS[v.sset] if v.kind != 'empty' else [] for v in vars_]
        env = '[' + ', '.join(v.expr for v in vars_) + ']'
        import itertools
        combos = list(itertools.product(*[vals for (_, vals, _) in cases])) if cases else [()]
        (q, dl, l, r), (q2, dl2, l2, r2) = start, end
        # statement
        derived = derived or {}
        sp = {p: p for (p, _, _) in cases}
        for dn, (dt, _) in derived.items():
            sp[dn] = dt
        stmt_a = self.expr(l, vars_, sp)
        stmt_r = self.expr(r, vars_, sp)
        stmt_a2 = self.expr(l2, vars_, sp)
        stmt_r2 = self.expr(r2, vars_, sp)
        h1 = 'hd' if dl else 'hdR'
        h2 = 'hd' if dl2 else 'hdR'
        qt = lambda qq: qq[0] if isinstance(qq, tuple) else self.qn(qq)
        qf = lambda qq, sub: qq[1](sub) if isinstance(qq, tuple) else qq
        lines = []
        lines.append('/-- %s -/' % doc if doc else '')
        lines.append('theorem %s %s :\n    %s.Reach (%s %s (%s)\n        (%s))\n      (%s %s (%s)\n        (%s)) := by'
                     % (name, binders, self.machine, h1, qt(q), stmt_a, stmt_r, h2, qt(q2), stmt_a2, stmt_r2))
        hvs = ' '.join('(Valid.cons %s' % (('(' + v.hyp + ')') if ' ' in v.hyp else v.hyp) for v in vars_)
        hv = hvs + ' (Valid.nil _)' + ')' * len(vars_)
        lines.append('  have hv : Valid [%s] %s := %s' % (', '.join(
            {'bits': 'bits', 'ALL': 'ALL', 'NB': 'NB'}[v.sset] for v in vars_), env, hv))
        # note: the sets of empty variables are bits
        if pre:
            lines.append(pre)
        kind = {(True, True): 'checkTT', (True, False): 'checkTF', (False, True): 'checkFT',
                (False, False): 'checkFF'}[(dl, dl2)]
        calls = []
        for combo in combos:
            sub = {cases[i][0]: combo[i] for i in range(len(cases))}
            for dn, (_, fn) in derived.items():
                sub[dn] = fn(sub)
            L = self.items(l, vars_, sub)
            R = self.items(r, vars_, sub)
            L2 = self.items(l2, vars_, sub)
            R2 = self.items(r2, vars_, sub)
            k = self.fuel(sets, qf(q, sub), L, R, dl, qf(q2, sub), L2, R2, dl2)
            if k is None:
                raise RuntimeError('%s: no path for case %s' % (name, sub))
            # the Lean fuel: mreachN with k steps; python reachN counts steps to reach target
            last = ('(by simp [cdn, dR, Item.den, List.getD, map_id_app, map_const_rep, Fn.app, rep_rep])'
                    if derived else '(by wsimp)')
            body = ('exact %s (env := %s) (E := []) (k := %d) hv trivial\n'
                    '        (ls := %s) (rs := %s)\n        (ls\' := %s) (rs\' := %s)\n'
                    '        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) '
                    % (kind, env, k, self.lean_items(L), self.lean_items(R), self.lean_items(L2),
                       self.lean_items(R2)))
            calls.append(body + last)
        if not cases:
            lines.append('  ' + calls[0])
        else:
            split = []
            for (p, vals, hyp) in cases:
                if sorted(vals) == [2, 3]:
                    split.append('rcases mem_bits %s with rfl | rfl' % hyp)
                elif sorted(vals) == [0, 2, 3]:
                    split.append('rcases %s with rfl | rfl | rfl' % hyp)
                else:
                    raise ValueError(vals)
            lines.append('  ' + ' <;> '.join(split) if len(split) > 1 else '  ' + split[0])
            for c in calls:
                lines.append('  · ' + c.replace('\n', '\n    '))
        return '\n'.join(x for x in lines if x != '') + '\n'


def explore(gen, vars_, start, stop, cases=(), limit=100000, sub=None, stopsym=None):
    """Run the symbolic machine from `start` = (state, dirL, leftToks, rightToks) until it first enters
    state `stop` (a name) or gets stuck; print the configuration with variable names."""
    sx = gen.sx
    sets = [SETS[v.sset] if v.kind != 'empty' else [] for v in vars_]
    q, dl, l, r = start
    sub = sub or {}
    c = sx.sc(q, gen.items(l, vars_, sub), gen.items(r, vars_, sub), dl)
    stopq = sx.Q[stop] if isinstance(stop, str) else None
    names = [v.name for v in vars_]
    k = 0
    while k < limit:
        if k > 0 and c[0] == stopq:
            if stopsym is None:
                break
            it = (c[1] if c[3] else c[2])
            if it and it[0] == ('s', SYM[stopsym]):
                break
        c2 = sx.mstep(sets, c)
        if c2 is None:
            break
        c = c2
        k += 1

    def sh(it):
        if it[0] == 's':
            return 'BM01'[it[1]]
        n = names[it[1]]
        return n if it[2] == 'id' else '%s->%s' % (n, 'BM01'[it[2]])
    q, l, r, dl = c
    return '%s steps=%d: %s %s %s' % (sx.QN.get(q, q), k, ' '.join(sh(x) for x in reversed(l)),
                                     '<' if dl else '>', ' '.join(sh(x) for x in r))
