"""Run a compiled 2-symbol native machine and compare beeps with the reference."""
import os
import subprocess
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'ref'))
import zp2_ref  # noqa: E402


def write_tbl(path, table, beep):
    with open(path, 'w') as f:
        f.write(f'{len(table)} {beep}\n')
        for s in table:
            f.write(' '.join('0 0 -1' if tr is None else
                             f"{tr[0]} {1 if tr[1] == 'R' else 0} {tr[2]}" for tr in s) + '\n')


def decode(lo, bits, enc):
    dec = {v: k for k, v in enc.items()}
    if lo % 2:
        lo -= 1
        bits = '0' + bits
    if len(bits) % 2:
        bits += '0'
    syms = ''.join(dec[(int(bits[i]), int(bits[i + 1]))] for i in range(0, len(bits), 2))
    f = syms.strip('B').split('M')
    return f[1], f[2]


def beeps(table, beep, enc, n, steps=10**11):
    path = os.path.join(HERE, '_tmp.tbl')
    write_tbl(path, table, beep)
    out = subprocess.run([os.path.join(HERE, 'psim'), path, str(steps), str(n)],
                         capture_output=True, text=True).stdout.split('\n')
    got = []
    for line in out:
        p = line.split()
        if len(p) == 3 and p[0].isdigit():
            got.append(decode(int(p[1]), p[2], enc))
        elif p:
            got.append(tuple(p))
    return got


def check(table, beep, enc, n=100):
    got = beeps(table, beep, enc, n)
    want = [(J, s) for _, J, s in zp2_ref.zp_beeps(max_beeps=n)]
    return got == want, got, want
