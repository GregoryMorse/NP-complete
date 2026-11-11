#!/usr/bin/env python3
"""Generate formal/ZP/Logic.lean: the 4-symbol logical machine native/zp2.py and the
compilation certificate (python3 formal/gen_logic.py).

Symbols are numbered B = 0, M = 1, '0' = 2, '1' = 3, so the pair encoding of
native/final.py is (s / 2, s % 2).  A logical transition code is 0 (undefined) or
1 + w + 4*d + 8*next with d = 1 for a right move.  Logical state 0 is the start.

The certificate gives, for each logical state q, the table state `entry q` and the
cell `side q` of its pair at which the table enters it, and for each defined
transition the number of table steps of its gadget.  Lean checks all of it
(ZP/Compile.lean).  CI regenerates the file and fails if it differs.
"""
import json, os, sys
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
sys.path[:0] = [os.path.join(ROOT, 'native'), os.path.join(ROOT, 'compiler')]
import compile2, final, tm, zp2  # noqa: E402

SYM = {'B': 0, 'M': 1, '0': 2, '1': 3}


def minimize_map(table, beep, start=0):
    """The state map of compiler/tm.py:minimize (same refinement, same numbering)."""
    n = len(table)
    cls = [0] * n
    cls[beep] = 1
    while True:
        sig, new = {}, [0] * n
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
    rep = {}
    for s in range(n):
        rep.setdefault(cls[s], s)
    order = [cls[start]] + sorted(set(cls) - {cls[start]}, key=lambda c: rep[c])
    idx = {c: i for i, c in enumerate(order)}
    return [idx[cls[s]] for s in range(n)]


def recover_cls(mt, mb, tab, beep):
    """Map the states of the Moore-minimal table `mt` to the states of the final table `tab` by
    following the defined transitions from the start (the final table only merges compatible states)."""
    cls = {0: 0}
    stack = [0]
    while stack:
        q = stack.pop()
        for a in (0, 1):
            tr = mt[q][a]
            if tr is None:
                continue
            ft = tab[cls[q]][a]
            assert ft is not None and ft[0] == tr[0] and ft[1] == tr[1], (q, a)
            if tr[2] in cls:
                assert cls[tr[2]] == ft[2], (q, a)
            else:
                cls[tr[2]] = ft[2]
                stack.append(tr[2])
    assert len(cls) == len(mt) and cls[mb] == beep
    return [cls[i] for i in range(len(mt))]


def read_tbl(name):
    lines = open(os.path.join(ROOT, 'machines', name + '.tbl')).read().split('\n')
    n, beep = map(int, lines[0].split())
    tab = []
    for q in range(n):
        f = list(map(int, lines[1 + q].split()))
        tab.append([None if f[3 * a + 2] < 0 else (f[3 * a], 'R' if f[3 * a + 1] else 'L', f[3 * a + 2])
                    for a in (0, 1)])
    return tab, beep


def gadget_len(tab, beep, e, hd, sym, target, nxt, enc_w):
    """Table steps from (e, cell hd) on the pair encoding sym until (nxt, cell target)."""
    tape = {0: sym // 2, 1: sym % 2}
    st, h = e, hd
    for k in range(1, 16):
        b = tape.get(h)
        rows = tab[st]
        if b is None:
            tr = rows[0]
        else:
            tr = rows[b]
        if b is not None:
            tape[h] = tr[0]
        h += 1 if tr[1] == 'R' else -1
        st = tr[2]
        if st == nxt and h == target:
            assert (tape[0], tape[1]) == enc_w
            return k
        assert st != beep
    raise AssertionError('gadget too long')


MACH = {
    # name: (native module, machines/ name, Lean identifier, file/namespace suffix, parent module)
    'zp': ('zp2', 'zp_native', 'zp', '', None),
    'zpp': ('zpp', 'zpp_native', 'zpp', 'PP', None),
    'zps': ('zps', 'zps_native', 'zps', 'PS', None),
    'zfac': ('zfac', 'zfactor_native', 'zfac', 'F', None),
    'zdl': ('zdl', 'zdlog_native', 'zdl', 'D', 'zfac'),
    'zgi': ('zgi', 'zgi_native', 'zgi', 'G', 'zfac'),
    'zntt': ('zntt', 'zntt_native', 'zntt', 'NTT', None),   # standalone: its own state names
    'zconp': ('zconp', 'zconp_native', 'zconp', 'Conp', None),
    'zmul': ('zmul', 'zmul_native', 'zmul', 'Mul', None),
    'zbpp': ('zbpp', 'zbpp_native', 'zbpp', 'BPP', None),
    'zppoly': ('zppoly', 'zppoly_native', 'zppoly', 'Poly', None),
    'zlp': ('zlp', 'zlp_native', 'zlp', 'LP', None),
    'zlnl': ('zlnl', 'zlnl_native', 'zlnl', 'LNL', None),
    'zmm': ('zmm', 'zmm_native', 'zmm', 'MM', 'zmul'),
}
MH = ('zlp', 'zlnl')
DERIVED = ('zpp', 'zps', 'zfac', 'zdl', 'zgi')   # machines whose changes define zpBase


def mh_core():
    """The transitions that the multihead machines zlp and zlnl have in common (same key, same value):
    the zp2 interpreter that neither changes and zmh's act, unit and erase states."""
    import zlp, zlnl
    a, b = zlp.build().d, zlnl.build().d
    return {k: v for k, v in a.items() if b.get(k) == v}


def mh_core_states():
    """The states of the common core that zp2 does not have, sorted: they come first in the numbering
    of zlp and of zlnl, so that lemmas about the core hold for both."""
    zs = set(zp2.build().states())
    d = mh_core()
    return sorted(({q for q, _ in d} | {v[2] for v in d.values()}) - zs)


def numbering(name):
    """State numbers: zp2 names keep zp2's numbers (also states the machine deletes), the
    parent's new states follow, then the machine's own new states, in `states()` order.
    zlp and zlnl: the common multihead core states come right after zp2's."""
    import importlib
    base = zp2.build().states()
    num = {q: i for i, q in enumerate(base)}
    if name in MH:
        for q in mh_core_states():
            num[q] = len(num)
    mod, _, _, _, parent = MACH[name]
    chain = ([MACH[parent][0]] if parent else []) + ([mod] if mod != 'zp2' else [])
    for mname in chain:
        for q in importlib.import_module(mname).build().states():
            if q not in num:
                num[q] = len(num)
    return num


def chunked(ident, typ, items):
    out = []
    ch = [items[i:i + 32] for i in range(0, len(items), 32)]
    for c, xs in enumerate(ch):
        out.append(f'def {ident}{c} : List {typ} :=\n  [' + ',\n   '.join(xs) + ']\n')
    out.append(f'def {ident} : List {typ} :=\n  ' + ' ++ '.join(f'{ident}{c}' for c in range(len(ch))) + '\n')
    return out


def write(fname, text):
    path = os.path.join(ROOT, 'formal', 'ZP', fname)
    open(path, 'w').write(text)
    return path


def gen_base(ident='zpBase', derived=None, fname='LogicBase.lean'):
    """zpBase: zp2 with every transition that some derived machine changes or deletes removed."""
    import importlib
    m = zp2.build()
    qs = m.states()
    num = {q: i for i, q in enumerate(qs)}
    vol = set()
    for mn in (derived or DERIVED):
        d = importlib.import_module(MACH[mn][0]).build().d
        vol |= {k for k in m.d if d.get(k) != m.d[k]}
    rows = []
    for q in qs:
        r = []
        for c in 'BM01':
            tr = m.d.get((q, c))
            if tr is None or (q, c) in vol:
                r.append(0)
            else:
                w, d, n = tr
                r.append(1 + SYM[w] + 4 * (d == 'R') + 8 * num[n])
        rows.append('[' + ', '.join(map(str, r)) + ']')
    body = chunked(ident + 'Rows', '(List Nat)', rows)
    body.append(f'/-- `zpLogic` without the {len(vol)} transitions that the derived native machines change. -/')
    beep = num[importlib.import_module('zmul').build().beep] if ident == 'zmBase' else num[m.beep]
    body.append(f'def {ident} : LTM := ⟨{ident}Rows, {beep}⟩\n')
    text = ('module\n\npublic import ZP.LTM\n\n@[expose] public section\n\n'
            '/-! Generated by `formal/gen_logic.py base` from `native/zp2.py` and the derived machines; do not edit. -/\n\n'
            'namespace ZP\n\n' + '\n'.join(body) + '\nend ZP\n')
    print(write(fname, text), len(vol), 'volatile transitions')


def gen_basemh():
    """mhBase: the transitions that zlp and zlnl have in common, over zp2's numbering followed by the
    core states (ZP/LogicBaseMH.lean, namespace QMH for the core states)."""
    m = zp2.build()
    d = mh_core()
    num = {q: i for i, q in enumerate(m.states())}
    for q in mh_core_states():
        num[q] = len(num)
    qs = sorted(num, key=num.get)
    rows = []
    for q in qs:
        r = []
        for c in 'BM01':
            tr = d.get((q, c))
            if tr is None:
                r.append(0)
            else:
                w, dd, n = tr
                r.append(1 + SYM[w] + 4 * (dd == 'R') + 8 * num[n])
        rows.append('[' + ', '.join(map(str, r)) + ']')
    body = chunked('mhBaseRows', '(List Nat)', rows)
    body.append('/-- The transitions that `zlpLogic` and `zlnlLogic` have in common: the part of `zp2` that neither changes\n'
                'and the multihead act, unit and erase states of `native/zmh.py`. -/')
    body.append(f'def mhBase : LTM := ⟨mhBaseRows, {num[m.beep]}⟩\n')
    core = mh_core_states()
    body.append('-- State numbers of the multihead core states (shared by `zlpLogic` and `zlnlLogic`).')
    body.append('namespace QMH\n' + ''.join(f'def {q} : Nat := {num[q]}\n' for q in core) + 'end QMH\n')
    text = ('module\n\npublic import ZP.LTM\n\n@[expose] public section\n\n'
            '/-! Generated by `formal/gen_logic.py basemh` from `native/zlp.py` and `native/zlnl.py`; do not edit. -/\n\n'
            'namespace ZP\n\n' + '\n'.join(body) + '\nend ZP\n')
    print(write('LogicBaseMH.lean', text), len(d), 'common transitions', len(core), 'core states')


def main(name='zp'):
    if name == 'base':
        return gen_base()
    if name == 'basemh':
        return gen_basemh()
    if name == 'baseconp':
        return gen_base('zcBase', DERIVED + ('zconp',), 'LogicBaseConp.lean')
    if name == 'basemul':
        return gen_base('zmBase', DERIVED + ('zmul',), 'LogicBaseMul.lean')
    import importlib
    modname, nat, ident, suf, _ = MACH[name]
    m = importlib.import_module(modname).build()
    qs0 = m.states()
    assert qs0[0] == m.start
    if name in ('zp', 'zntt'):
        qs = qs0
        num = {q: i for i, q in enumerate(qs)}
    else:
        num = numbering(name)
        qs = sorted(num, key=num.get)
    present = set(qs0)
    sd = final.sides(m, modname)
    t, b, names = compile2.compile_sides(m, final.ENC, sd)
    mm = minimize_map(t, b)
    tab, beep = read_tbl(nat)
    jpath = os.path.join(ROOT, 'native', f'exact_{nat}.json')
    if os.path.exists(jpath):
        cls = json.load(open(jpath))
    else:
        cls = recover_cls(*tm.minimize(t, b), tab, beep)
    entry = [cls[mm[names[('P', q)]]] if q in present else 0 for q in qs]
    side = [sd[q] if q in present else 0 for q in qs]
    enc = {s: final.ENC[c] for c, s in SYM.items()}
    assert all(enc[s] == (s // 2, s % 2) for s in range(4))
    rows, glen = [], []
    for q in qs:
        r, g = [], []
        for c in 'BM01':
            tr = m.d.get((q, c)) if q in present else None
            if tr is None:
                r.append(0)
                g.append(0)
                continue
            w, d, n = tr
            r.append(1 + SYM[w] + 4 * (d == 'R') + 8 * num[n])
            target = (2 if d == 'R' else -2) + sd[n]
            g.append(gadget_len(tab, beep, entry[num[q]], sd[q], SYM[c], target,
                                entry[num[n]], enc[SYM[w]]))
        rows.append('[' + ', '.join(map(str, r)) + ']')
        glen.append('[' + ', '.join(map(str, g)) + ']')
    body = []
    body += chunked(f'{ident}LogicRows', '(List Nat)', rows)
    body.append(f'/-- `native/{modname}.py` ({len(qs0)} states, beep state {num[m.beep]}). -/')
    body.append(f'def {ident}Logic : LTM := ⟨{ident}LogicRows, {num[m.beep]}⟩\n')
    body.append('/-- Table state entering logical state `q`. -/')
    body.append(f'def {ident}Entry : List Nat :=\n  [' + ', '.join(map(str, entry)) + ']\n')
    body.append('/-- Cell of the pair (0 left, 1 right) at which the table enters `q`. -/')
    body.append(f'def {ident}Side : List Nat :=\n  [' + ', '.join(map(str, side)) + ']\n')
    body += chunked(f'{ident}Glen', '(List Nat)', glen)
    if name == 'zntt':
        body.append('-- State numbers of `zNttLogic`, by their names in `native/zntt.py`.')
        body.append('namespace QNTT\n' + ''.join(f'def {q} : Nat := {num[q]}\n' for q in qs) + 'end QNTT\n')
    elif name == 'zp':
        body.append('-- State numbers of `zpLogic`, by their names in `native/zp2.py`.')
        body.append('namespace Q\n' + ''.join(f'def {q} : Nat := {num[q]}\n' for q in qs) + 'end Q\n')
    else:
        core = set(mh_core_states()) if name in MH else set()
        new = [q for q in qs if num[q] >= 129 and q not in core]
        body.append(f'-- State numbers of the states that are new in `{modname}` (zp2 names keep their `Q` number).')
        body.append(f'namespace Q{suf}\n' + ''.join(f'def {q} : Nat := {num[q]}\n' for q in new) + f'end Q{suf}\n')
    fname = 'Logic' + suf + '.lean'
    text = ('module\n\npublic import ZP.LTM\n\n@[expose] public section\n\n'
            f'/-! Generated by `formal/gen_logic.py{"" if name == "zp" else " " + name}` from `native/{modname}.py` and the build; do not edit. -/\n\n'
            'namespace ZP\n\n' + '\n'.join(body) + '\nend ZP\n')
    path = write(fname, text)
    print(path, len(qs0), 'logical states', len(qs), 'slots, max gadget',
          max(max(map(int, g[1:-1].split(', '))) for g in glen))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'zp')
