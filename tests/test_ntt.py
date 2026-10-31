"""Circuit search of compiler/ntt_cm.py vs the brute force of ref/ntt_ref.py."""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [os.path.join(HERE, '..', 'compiler'), os.path.join(HERE, '..', 'ref')]
import ntt_cm                  # noqa: E402
import ntt_ref as T            # noqa: E402

CASES = [(1, 0), (1, 1), (2, 0), (2, 1), (2, 2), (3, 0)]


def write_cm(prog, path, jreg, sreg):
    idx = {r: i for i, r in enumerate(prog.regs)}
    with open(path, 'w') as f:
        f.write(f"{len(prog)} {len(prog.regs)} {prog.entry} {idx[jreg]} {idx[sreg]}\n")
        for ins in prog.code:
            if ins[0] == 'INC':
                f.write(f'0 {idx[ins[1]]} {ins[2]}\n')
            elif ins[0] == 'DEC':
                f.write(f'1 {idx[ins[1]]} {ins[2]} {ins[3]}\n')
            else:
                f.write(f'2 {ins[1]}\n')


def main():
    import subprocess
    import tempfile
    sim = os.path.join(HERE, '..', 'sim', 'cmsim')
    subprocess.check_call(['gcc', '-O2', '-o', sim, sim + '.c'])
    # a final beep marks completion of every case
    cases = CASES + [(1, 0)]
    p = ntt_cm.harness(cases).assemble()
    path = os.path.join(tempfile.mkdtemp(), 'h.cm')
    write_cm(p, path, 'Ix', 'Ix')
    want = [i + 1 for i, (n, s) in enumerate(cases) if T.has_circuit(n, s)]
    out = subprocess.run([sim, path, str(10**11), str(len(want))],
                         capture_output=True, text=True).stdout
    got = [int(l.split()[1]) for l in out.split('\n') if l.strip()]
    ok = got == want
    print(f'NTT circuit search: cases {CASES}: exists at {got} (reference {want}) '
          f'-> {"OK" if ok else "FAIL"}')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
