import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'ref'))
import logic, zp2, zp2_ref


def decode(tape):
    lo = min(i for i, c in tape.items() if c != 'B')
    s = ''
    i = lo
    while tape.get(i, 'B') != 'B':
        s += tape[i]; i += 1
    f = s.split('M')
    return f[1], f[2]


def beeps(n, steps=10**8):
    m = zp2.build()
    out = []
    def cb(tape, h):
        out.append(decode(tape)); return len(out) < n
    r = logic.run(m, steps, cb)
    return out, r


if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    got, r = beeps(n)
    want = [(J, s) for _, J, s in zp2_ref.zp_beeps(max_beeps=n)]
    print(r[0], r[4], logic.show(r[2], r[3])[:200] if r[0] == 'halt' else '')
    print('got ', got)
    print('want', want)
