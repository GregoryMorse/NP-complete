"""Python driver for esim.c (logical machine event runner)."""
import os
import subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
SY = 'BM01'


def write_table(m, path):
    qs = m.states()
    ix = {q: i for i, q in enumerate(qs)}
    with open(path, 'w') as f:
        f.write(f'{len(qs)}\n')
        for q in qs:
            for a in SY:
                tr = m.d.get((q, a))
                if tr is None:
                    f.write('0 0 -1\n')
                else:
                    f.write(f'{SY.index(tr[0])} {1 if tr[1] == "R" else 0} {ix[tr[2]]}\n')
    return ix


def events(m, evstates, maxev, tape='', head=0, start=None, maxsteps=10**11, path=None):
    """[(state name, step, tape string)] for the first maxev entries into evstates."""
    path = path or os.path.join(HERE, '_esim.ltab')
    ix = write_table(m, path)
    names = {i: q for q, i in ix.items()}
    out = subprocess.run([os.path.join(HERE, 'esim'), path, str(maxsteps), str(ix[start or m.start]),
                          tape or 'B', str(head), ','.join(str(ix[q]) for q in evstates), str(maxev)],
                         capture_output=True, text=True).stdout.split('\n')
    res = []
    for line in out:
        p = line.split()
        if not p:
            continue
        if p[0].isdigit():
            res.append((names[int(p[0])], int(p[1]), p[2] if len(p) > 2 else ''))
        else:
            res.append(tuple(p))
    return res
