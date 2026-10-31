#!/usr/bin/env python3
"""Turn Lean diagnostics in a build log into GitHub annotations."""
import re
import sys

text = open(sys.argv[1], encoding='utf-8', errors='replace').read()
pat = re.compile(r'^(?:error|warning): (\S+?\.lean):(\d+):(\d+): (.*?)(?=^(?:error|warning|info|✖|⚠|✔|Build|Some)|\Z)',
                 re.M | re.S)
n = 0
for m in pat.finditer(text):
    path, line, col, msg = m.groups()
    if 'declaration uses' in msg and 'sorry' in msg:
        continue
    msg = msg.strip().replace('%', '%25').replace('\r', '').replace('\n', '%0A')
    print(f'::error file=formal/{path},line={line},col={col}::{msg[:3000]}')
    n += 1
if n == 0:
    tail = text[-3000:].replace('%', '%25').replace('\n', '%0A')
    print(f'::error::{tail}')
