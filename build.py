#!/usr/bin/env python3
"""Reproducible build of Z_P and its test variants.

    python3 build.py            # writes machines/*.{tbl,txt,json}
    python3 build.py --check    # also runs the differential tests (needs gcc)

Output per variant:
  machines/<name>.txt   the transition table, one line, states '_'-separated,
                        each state 'w0M0n0,w1M1n1' (n = state number, 0 = start)
  machines/<name>.tbl   the same, simulator input format (sim/tmsim.c)
  machines/<name>.json  state count, beep state, register order, SHA-256
"""
import hashlib
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [os.path.join(ROOT, 'compiler'), os.path.join(ROOT, 'ref')]

import tm          # noqa: E402
import zp_cm       # noqa: E402
import zp_ref      # noqa: E402

A = zp_ref.assemble
# controlled candidate lists (brief §5.3): known-wrong candidates with known
# first counterexamples, then (for the P-language) one known-correct one.
REJECT_ALL = 1                                   # empty code
ACCEPT_ALL = A([(1, 1, 0)] * 2)
RUN_RIGHT = A([(0, 1, 1)] * 2)                   # never halts -> TIMEOUT
FIRST_CELL = A([(0, 0, 0), (1, 0, 0)])           # accept iff first cell is 1
CTL_NONEMPTY = [REJECT_ALL, ACCEPT_ALL, RUN_RIGHT, FIRST_CELL]
CTL_L = [ACCEPT_ALL, RUN_RIGHT, REJECT_ALL, FIRST_CELL]

VARIANTS = {
    'zp': dict(truth='L'),
    'pswap_nonempty': dict(truth='nonempty'),
    'pswap_odd': dict(truth='odd'),
    'ctl_nonempty': dict(truth='nonempty', candidates=CTL_NONEMPTY),
    'ctl_zp': dict(truth='L', candidates=CTL_L),
}


def build_variant(name, opts, iters=40000):
    prog = zp_cm.build(**opts).assemble()
    order, _ = tm.optimize_order(prog, iters=iters)
    table, info = tm.compile_cm(prog, order)
    table, beep = tm.minimize(table, info['beep'])
    std = tm.to_standard(table)
    meta = {
        'name': name,
        'counter_instructions': len(prog),
        'registers': len(order),
        'states': len(table),
        'beep_state': beep,
        'register_order': order,
        'sha256': hashlib.sha256(std.encode()).hexdigest(),
        'format': "states '_'-separated; state = 'w0M0n0,w1M1n1'; '---' undefined; start = 0",
    }
    os.makedirs(os.path.join(ROOT, 'machines'), exist_ok=True)
    idx = {r: i for i, r in enumerate(prog.regs)}
    with open(os.path.join(ROOT, 'machines', name + '.cm'), 'w') as f:
        f.write(f"{len(prog)} {len(prog.regs)} {prog.entry} {idx['J']} {idx['S']}\n")
        for ins in prog.code:
            if ins[0] == 'INC':
                f.write(f'0 {idx[ins[1]]} {ins[2]}\n')
            elif ins[0] == 'DEC':
                f.write(f'1 {idx[ins[1]]} {ins[2]} {ins[3]}\n')
            else:
                f.write(f'2 {ins[1]}\n')
    with open(os.path.join(ROOT, 'machines', name + '.txt'), 'w') as f:
        f.write(std + '\n')
    with open(os.path.join(ROOT, 'machines', name + '.tbl'), 'w') as f:
        f.write(f'{len(table)} {beep}\n')
        for s in table:
            f.write(' '.join('-1 0 -1' if tr is None else
                             f"{tr[0]} {1 if tr[1] == 'R' else 0} {tr[2]}" for tr in s) + '\n')
    with open(os.path.join(ROOT, 'machines', name + '.json'), 'w') as f:
        json.dump(meta, f, indent=1)
    return meta


def main():
    for name, opts in VARIANTS.items():
        m = build_variant(name, opts)
        print(f"{name:16s} states={m['states']:5d} cm={m['counter_instructions']} "
              f"regs={m['registers']} beep={m['beep_state']} sha256={m['sha256'][:16]}")
    if '--check' in sys.argv:
        sys.exit(subprocess.call([sys.executable, os.path.join(ROOT, 'tests', 'diff_tm_ref.py')]))


if __name__ == '__main__':
    main()
