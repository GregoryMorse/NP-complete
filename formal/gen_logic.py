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
import compile2, final, zp2  # noqa: E402

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


def main():
    m = zp2.build()
    qs = m.states()
    assert qs[0] == m.start
    num = {q: i for i, q in enumerate(qs)}
    sd = final.sides(m, 'zp2')
    t, b, names = compile2.compile_sides(m, final.ENC, sd)
    mm = minimize_map(t, b)
    cls = json.load(open(os.path.join(ROOT, 'native', 'exact_zp_native.json')))
    tab, beep = read_tbl('zp_native')
    entry = [cls[mm[names[('P', q)]]] for q in qs]
    side = [sd[q] for q in qs]
    enc = {s: final.ENC[c] for c, s in SYM.items()}
    assert all(enc[s] == (s // 2, s % 2) for s in range(4))
    rows, glen = [], []
    for q in qs:
        r, g = [], []
        for c in 'BM01':
            tr = m.d.get((q, c))
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

    def chunked(ident, typ, items):
        out = []
        ch = [items[i:i + 32] for i in range(0, len(items), 32)]
        for c, xs in enumerate(ch):
            out.append(f'def {ident}{c} : List {typ} :=\n  [' + ',\n   '.join(xs) + ']\n')
        out.append(f'def {ident} : List {typ} :=\n  ' + ' ++ '.join(f'{ident}{c}' for c in range(len(ch))) + '\n')
        return out
    body = []
    body += chunked('zpLogicRows', '(List Nat)', rows)
    body.append(f'/-- `native/zp2.py` ({len(qs)} states, beep state {num[m.beep]}). -/')
    body.append(f'def zpLogic : LTM := ⟨zpLogicRows, {num[m.beep]}⟩\n')
    body.append('/-- Table state entering logical state `q`. -/')
    body.append('def zpEntry : List Nat :=\n  [' + ', '.join(map(str, entry)) + ']\n')
    body.append('/-- Cell of the pair (0 left, 1 right) at which the table enters `q`. -/')
    body.append('def zpSide : List Nat :=\n  [' + ', '.join(map(str, side)) + ']\n')
    body += chunked('zpGlen', '(List Nat)', glen)
    body.append('/-- State numbers of `zpLogic`, by their names in `native/zp2.py`. -/')
    body.append('namespace Q\n' + ''.join(f'def {q} : Nat := {num[q]}\n' for q in qs) + 'end Q\n')
    text = ('module\n\npublic import ZP.LTM\n\n@[expose] public section\n\n'
            '/-! Generated by `formal/gen_logic.py` from `native/zp2.py` and the build; do not edit. -/\n\n'
            'namespace ZP\n\n' + '\n'.join(body) + '\nend ZP\n')
    path = os.path.join(ROOT, 'formal', 'ZP', 'Logic.lean')
    open(path, 'w').write(text)
    print(path, len(qs), 'logical states, max gadget', max(max(map(int, g[1:-1].split(', '))) for g in glen))


if __name__ == '__main__':
    main()
