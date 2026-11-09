#!/usr/bin/env python3
"""Capacity check for the Z_MUL switch (plan 07, "Capacity condition").

Runs the logical machine native/zmul.py from the run-start layout
    M M J M [s] M M 1^(|s|+1) (M 1)^|J| B M^|J|      (state GC, head on s)
for random (J, s) in C (capsim.c), and compares the outcome (DP31 = proper halt with a
correct product) with ref/zmul_ref.correct.  It also reports, per run:
  minslack  blank cells left of every cell the pop deposits (mLL0/mLL1 writing), before
            the next non-blank; -1 would mean the deposit ran past the code (overflow);
  rhodec    how often the room rho (cells strictly between the code's right end and the
            head marker H)
            decreased from one guest step to the next;
  minrho    its minimum.
rho is measured at each entry to state FBACK (the fuel decrement that starts every guest
step): from the leftmost non-blank skip the code bits, then count up to the first M (= H).

usage: python3 run.py SEED N MAXLEN_J MAXLEN_S
"""
import os, sys, json, random, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..', '..', '..')
sys.path[:0] = [os.path.join(ROOT, 'native'), os.path.join(ROOT, 'ref')]
import zmul, zmul_ref

m = zmul.build()
QS = m.states()
IX = {q: i for i, q in enumerate(QS)}
TBL = os.path.join(HERE, 'zmul.ltbl')
BIN = os.path.join(HERE, 'capsim')


def prepare():
    out = [str(len(QS))]
    for q in QS:
        for a in 'BM01':
            tr = m.d.get((q, a))
            out.append('0 0 -1' if tr is None else
                       f"{'BM01'.index(tr[0])} {1 if tr[1] == 'R' else 0} {IX[tr[2]]}")
    open(TBL, 'w').write('\n'.join(out) + '\n')
    if not os.path.exists(BIN):
        subprocess.check_call(['gcc', '-O2', '-o', BIN, os.path.join(HERE, 'capsim.c')])


def mrun(J, s, maxsteps=4 * 10**9):
    left = 'MM' + J + 'M'
    tape = left + s + 'MM' + '1' * (len(s) + 1) + 'M1' * len(J) + 'B' + 'M' * len(J)
    args = [BIN, TBL, str(maxsteps)] + [str(IX[q]) for q in ('GC', 'DP30', 'DP31', 'mLL0', 'mLL1')]
    args += [tape, str(len(left)), str(IX['FBACK'])]
    return subprocess.run(args, capture_output=True, text=True).stdout.split()


if __name__ == '__main__':
    prepare()
    random.seed(int(sys.argv[1])); N = int(sys.argv[2]); jl = int(sys.argv[3]); sl = int(sys.argv[4])
    bad = pops = 0; worst = None
    for _ in range(N):
        J = ''.join(random.choice('01') for _ in range(random.randint(1, jl)))
        s = ''.join(random.choice('01') for _ in range(random.randint(0, sl)))
        o = mrun(J, s)
        if o[0] != 'OUT':
            print('ABNORMAL', J, s, o); continue          # STEPS: step cap reached
        if (o[1] == '1') != zmul_ref.correct(J, s):
            print('MISMATCH', J, s, o); bad += 1
        if int(o[5]):
            print('RHODEC', J, s, o); bad += 1
        if int(o[3]) == -1:
            print('OVERFLOW', J, s, o); bad += 1
        if int(o[4]) and (worst is None or int(o[3]) < worst[0]):
            worst = (int(o[3]), J, s, int(o[4]))
        pops += int(o[4])
    print('N', N, 'bad', bad, 'deposits', pops, 'min slack', worst)
