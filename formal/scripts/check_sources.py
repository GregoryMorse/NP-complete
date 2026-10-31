#!/usr/bin/env python3
"""Pre-build checks mirroring Palomar's source rules, plus a sorry census.

* every .lean file starts with the `module` header (comments allowed before it);
* no file exceeds 10,000 lines;
* prints each `sorry` outside Challenge.lean (Challenge's are deliberate).
"""
import pathlib
import re
import sys

root = pathlib.Path(__file__).resolve().parents[1]
bad = False
sorries = []
for p in sorted(root.rglob('*.lean')):
    if '.lake' in p.parts:
        continue
    text = p.read_text(encoding='utf-8')
    body = re.sub(r'/-.*?-/', lambda m: '\n' * m.group().count('\n'), text, flags=re.S)
    body = re.sub(r'--[^\n]*', '', body)
    if not body.lstrip().startswith('module'):
        print(f'{p.relative_to(root)}: missing module header')
        bad = True
    if text.count('\n') > 10000:
        print(f'{p.relative_to(root)}: over 10,000 lines')
        bad = True
    if p.name != 'Challenge.lean':
        for i, line in enumerate(body.split('\n'), 1):
            if re.search(r'\bsorry\b', line):
                sorries.append(f'{p.relative_to(root)}:{i}')
print(f'open sorries outside Challenge.lean: {len(sorries)}')
for s in sorries:
    print('  ' + s)
sys.exit(1 if bad else 0)
