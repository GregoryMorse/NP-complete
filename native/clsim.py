import subprocess, sys, os
sys.path.insert(0, '../ref')
SY = 'BM01'

def write_table(m, path):
    qs = m.states(); ix = {q: i for i, q in enumerate(qs)}
    with open(path, 'w') as f:
        f.write(f'{len(qs)}\n')
        for q in qs:
            for a in SY:
                tr = m.d.get((q, a))
                if tr is None: f.write('0 0 -1\n')
                else: f.write(f'{SY.index(tr[0])} {1 if tr[1]=="R" else 0} {ix[tr[2]]}\n')
    return ix

def instance(path, ix, beep, J, s, maxsteps=10**10, start='W1'):
    tape = 'M' + J + 'M' + s
    out = subprocess.run(['./lsim', path, str(maxsteps), str(ix[start]), str(ix['SINC']),
                          str(ix[beep]), tape, str(len(tape))], capture_output=True, text=True).stdout.split()
    return {'OK': True, 'BAD': False}.get(out[0], out)
