#!/usr/bin/env python3
"""Check a commit before it is submitted to Palomar (python3 formal/scripts/palomar_precheck.py).

Each check below is something a past submission was rejected or marked down for.

Mechanical (Palomar refuses the submission):
* Challenge.lean is at most 100 KiB and 1,000 lines;
* comparator.json has exactly Palomar's keys, and only the allowed axioms;
* every .lean file has the `module` header (see also check_sources.py).

Consistency (the reviewer reads the prose against the theorems):
* the theorems of Challenge.lean, Solution.lean, comparator.json, the `lean:` entries of
  formalization.yaml and the theorem table of formal/README.md are the same set;
* every "<n> Lean formalizations", "<n> Challenge theorems", "each of the <n>" in README.md,
  formal/README.md and formalization.yaml states the number of Challenge theorems;
* the state counts in README.md, formal/README.md and docs/native.md match machines/*.json;
* no stale phrase ("not yet formalized", "withdrawn", "degenerate", placeholders) remains.
"""
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
F = ROOT / 'formal'
WORDS = {w: i for i, w in enumerate(
    'zero one two three four five six seven eight nine ten eleven twelve thirteen fourteen '
    'fifteen sixteen seventeen eighteen nineteen twenty'.split())}
errors = []


def err(msg):
    errors.append(msg)


def read(p):
    return (ROOT / p).read_text(encoding='utf-8')


# --- mechanical -------------------------------------------------------------
ch = read('formal/Challenge.lean')
if len(ch.encode()) > 100 * 1024:
    err(f'Challenge.lean is {len(ch.encode())} bytes (cap 102400)')
if ch.count('\n') > 1000:
    err(f'Challenge.lean has {ch.count(chr(10))} lines (cap 1000)')

comp = json.loads(read('formal/comparator.json'))
keys = {'challenge_module', 'solution_module', 'theorem_names', 'definition_names', 'permitted_axioms'}
if set(comp) != keys:
    err(f'comparator.json keys {sorted(comp)} != {sorted(keys)}')
if not set(comp.get('permitted_axioms', [])) <= {'propext', 'Quot.sound', 'Classical.choice'}:
    err(f"comparator.json axioms {comp.get('permitted_axioms')}")

for p in sorted(F.rglob('*.lean')):
    if '.lake' in p.parts:
        continue
    body = re.sub(r'/-.*?-/', '', p.read_text(encoding='utf-8'), flags=re.S)
    body = re.sub(r'--[^\n]*', '', body)
    if not body.lstrip().startswith('module'):
        err(f'{p.relative_to(ROOT)}: missing module header')

# --- theorem sets -----------------------------------------------------------
thm = re.compile(r'^theorem\s+(\S+)', re.M)
sets = {
    'Challenge.lean': {c.split()[0] for c in re.split(r'^theorem\s+', ch, flags=re.M)[1:]
                       if re.search(r'\bsorry\b', re.split(r'^(?:theorem|def|/--)', c, flags=re.M)[0])},
    'Solution.lean': set(thm.findall(read('formal/Solution.lean'))),
    'comparator.json': set(comp['theorem_names']),
    'formalization.yaml': set(re.findall(r'^\s*lean:\s*"([^"]+)"', read('formal/formalization.yaml'), re.M)),
    'formal/README.md': {m for m in re.findall(r'^\|[^|]*\|\s*`([^`]+)`', read('formal/README.md'), re.M)
                         if m.startswith('ZP.')},
}
ref = sets['comparator.json']
n = len(ref)
if len(comp['theorem_names']) != n:
    err('comparator.json lists a theorem twice')
for name, s in sets.items():
    if s != ref:
        err(f'{name}: theorems differ from comparator.json: missing {sorted(ref - s)}, extra {sorted(s - ref)}')

# --- counts and stale phrases in prose ----------------------------------------
PROSE = ['README.md', 'formal/README.md', 'formal/formalization.yaml', 'docs/native.md']
count_pat = re.compile(r'\b(\w+)\s+(?:Lean formalizations|Challenge\s+theorems|advertised machines)'
                       r'|\beach of the\s+(\w+)', re.I)
stale = re.compile(r'not yet formalized|withdrawn|degenerate|known defect|ZMULN|TODO|FIXME', re.I)
for p in PROSE:
    text = read(p)
    for m in count_pat.finditer(text):
        w = (m.group(1) or m.group(2)).lower()
        if w in ('the', 'all', 'these', 'its', 'other'):
            continue
        v = WORDS.get(w, int(w) if w.isdigit() else None)
        if v is not None and v != n:
            line = text[:m.start()].count('\n') + 1
            err(f'{p}:{line}: says "{m.group(0)}", but there are {n} Challenge theorems')
    for m in stale.finditer(text):
        line = text[:m.start()].count('\n') + 1
        err(f'{p}:{line}: stale phrase "{m.group(0)}"')

# --- state counts --------------------------------------------------------------
states = {p.stem: json.loads(p.read_text())['states'] for p in (ROOT / 'machines').glob('*.json')}
readme = read('README.md')
for m in re.finditer(r'^\|[^|]*\|\s*\**(\w+)\**\s*\|\s*`machines/(\w+)\.txt`', readme, re.M):
    if m.group(2) in states and m.group(1) != str(states[m.group(2)]):
        err(f'README.md: {m.group(2)} listed with {m.group(1)} states, table has {states[m.group(2)]}')
native = read('docs/native.md')
for m in re.finditer(r'`native/(\w+)\.py`, (\d+) states', native):
    mod = m.group(1)
    tbl = {'zp2': 'zp_native', 'zfac': 'zfactor_native', 'zdl': 'zdlog_native', 'zps': 'zps_native'}.get(
        mod, mod + '_native')
    if tbl in states and int(m.group(2)) != states[tbl]:
        err(f'docs/native.md: {mod} listed with {m.group(2)} states, table has {states[tbl]}')
FR = {'Z_P': 'zp_native', 'Z_PP': 'zpp_native', 'Z_BPP': 'zbpp_native', 'Z_PSPACE': 'zps_native',
      'Z_FACTOR': 'zfactor_native', 'Z_DLOG': 'zdlog_native', 'Z_GI': 'zgi_native', 'Z_NTT': 'zntt_native',
      'Z_MUL': 'zmul_native', 'Z_PPOLY': 'zppoly_native', 'Z_MATMUL': 'zmm_native', 'Z_LP': 'zlp_native',
      'Z_LNL': 'zlnl_native', 'Z_coNP': 'zconp_native', 'twin primes': 'twinprime_native'}
for m in re.finditer(r'^\| ([^|(]+?) \((\w+)\) \| `ZP\.', read('formal/README.md'), re.M):
    tbl = FR.get(m.group(1))
    if tbl is None:
        err(f'formal/README.md: unknown machine row "{m.group(1)}"')
    elif str(states.get(tbl)) != m.group(2):
        err(f'formal/README.md: {m.group(1)} listed with {m.group(2)} states, table has {states.get(tbl)}')

if errors:
    print('\n'.join(errors))
    sys.exit(1)
print(f'palomar precheck: ok ({n} theorems)')
