#!/usr/bin/env python3
"""Generate Challenge.lean and ZP/AllDefs.lean: a self-contained module (Lean core only) made of the trusted
definition files in the import closure of the old Challenge, followed by `challenge_statements.lean.in`.

Palomar compiles the Challenge alone against Lean core, so it may not import project modules.
ZP/AllDefs.lean is the same definition block as a project module, so that the development and
the Challenge elaborate the definitions identically (Lean reuses equal `match` helpers within one
module, which would otherwise make the compiled terms differ).  The per-file sources ZP/Defs*.lean,
ZP/Table*.lean are the generator inputs; nothing imports them.
`python3 gen_challenge.py --check` verifies that Challenge.lean is up to date."""
import re, sys
from pathlib import Path

ROOT = Path(__file__).parent
ROOTS = ['ZP.Defs', 'ZP.Table', 'ZP.DefsPP', 'ZP.DefsBPP', 'ZP.DefsPS', 'ZP.DefsF', 'ZP.DefsD', 'ZP.DefsG',
         'ZP.DefsNTT', 'ZP.TableNTT', 'ZP.DefsTwin', 'ZP.TableTwin', 'ZP.DefsMul', 'ZP.TableMul',
         'ZP.DefsConp', 'ZP.TableConp']
WIDTH = 600

def path(m): return ROOT / (m.replace('.', '/') + '.lean')

def imports(m):
    return re.findall(r'^public import (\S+)$', path(m).read_text(), re.M)

order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for i in imports(m): visit(i)
    order.append(m)
for r in ROOTS: visit(r)

row = re.compile(r'^\s*\[?\(\d+, \d+\)(,|\])*$')

def pack(lines):
    out, buf, i = [], None, 0
    for ln in lines:
        s = ln.strip()
        if row.match(ln):
            if buf is None:
                buf = '  ' + s if s.startswith('[') else '   ' + s
            elif len(buf) + 1 + len(s) > WIDTH:
                out.append(buf); buf = '   ' + s
            else:
                buf += ' ' + s
            if s.endswith(']'):
                if out and out[-1].endswith(':=') and out[-1].startswith('def '):
                    out[-1] += ' ' + buf.strip()
                else:
                    out.append(buf)
                buf = None
        else:
            if buf is not None: out.append(buf); buf = None
            out.append(ln.rstrip())
    return out

body = []
for m in order:
    t = path(m).read_text().split('\n')
    k = next(i for i, l in enumerate(t) if l.startswith('@[expose] public section'))
    assert all(l.startswith(('module', 'public import', '')) and not l.strip().startswith('import ') for l in t[:k])
    body.append('/- ## ' + m + ' -/')
    body += pack(t[k + 1:])
    body.append('')
defs = '\n'.join(body)
defs = re.sub(r'\n{3,}', '\n\n', defs)
defs = re.sub(r'(/- ## \S+ -/\n)\n', r'\1', defs)
defs = re.sub(r'(namespace ZP\n)\n', r'\1', defs)
defs = re.sub(r'(\]\n)\n(?=def \w+Rows\d+ )', r'\1', defs)
stm = (ROOT / 'challenge_statements.lean.in').read_text()
out = ('module\n\n@[expose] public section\n\n' + defs.strip('\n') + '\n\n' + stm)
alldefs = 'module\n\n@[expose] public section\n\n' + defs.strip('\n') + '\n'
f = ROOT / 'Challenge.lean'
fa = ROOT / 'ZP' / 'AllDefs.lean'
if '--check' in sys.argv:
    if f.read_text() != out or fa.read_text() != alldefs:
        sys.exit('Challenge.lean / ZP/AllDefs.lean are out of date: run python3 gen_challenge.py')
    print('Challenge.lean up to date')
else:
    f.write_text(out)
    fa.write_text(alldefs)
    print(len(out.splitlines()), 'lines', len(out.encode()), 'bytes')
