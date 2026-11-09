"""Write the design as machines/twinprime_native.{txt,tbl,json}."""
import hashlib, json, os, sys
from design import T, ORDER, START, BEEP

assert ORDER[0] == START
idx = {s: i for i, s in enumerate(ORDER)}


def act(a):
    return '---' if a is None else f'{a[0]}{a[1]}{idx[a[2]]}'


def main(out):
    txt = '_'.join(','.join(act(a) for a in T[s]) for s in ORDER)
    tbl = [f'{len(ORDER)} {idx[BEEP]}']
    for s in ORDER:
        row = []
        for a in T[s]:
            row += ['0', '0', '-1'] if a is None else [str(a[0]), '1' if a[1] == 'R' else '0', str(idx[a[2]])]
        tbl.append(' '.join(row))
    # bbchallenge standard text (A = start); its beep is the beep *state*
    L = lambda i: chr(ord('A') + i)
    std = '_'.join(''.join('---' if a is None else f'{a[0]}{a[1]}{L(idx[a[2]])}' for a in T[s]) for s in ORDER)
    meta = {'name': 'twinprime_native', 'states': len(ORDER), 'start': 0, 'beep': idx[BEEP],
            'sha256': hashlib.sha256(txt.encode()).hexdigest(),
            'reference': 'twin/design.py (lesser_twins)', 'design': 'twin/README.md',
            'format': "states '_'-separated; state = 'w0M0n0,w1M1n1'; '---' undefined; start = 0",
            'state_names': ORDER, 'standard_text': std,
            'property': 'visits the beep state exactly once per lesser twin prime p >= 3; '
                        'quasihalts iff there are finitely many twin primes'}
    os.makedirs(out, exist_ok=True)
    open(f'{out}/twinprime_native.txt', 'w').write(txt + '\n')
    open(f'{out}/twinprime_native.tbl', 'w').write('\n'.join(tbl) + '\n')
    open(f'{out}/twinprime_native.json', 'w').write(json.dumps(meta, indent=1) + '\n')
    return std


if __name__ == '__main__':
    print(main(sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'machines')))
