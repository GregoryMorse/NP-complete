import sys
import zntt

m = zntt.build()


def run(content, state, keys, stops, maxs=20000, hpos=None):
    tape = {i: c for i, c in enumerate(content)}
    h = len(content) - 1 if hpos is None else hpos
    q = state

    def show():
        lo, hi = min(tape), max(tape)
        return ''.join(('[' if i == h else '') + tape.get(i, 'B') for i in range(lo, hi + 1))
    for i in range(maxs):
        if q in keys:
            print(i, q, show())
        if q in stops and i > 0:
            print(i, q, show())
            break
        tr = m.d.get((q, tape.get(h, 'B')))
        if tr is None:
            print('halt', q)
            break
        tape[h], mv, q = tr
        h += 1 if mv == 'R' else -1


if __name__ == '__main__':
    content, state = sys.argv[1], sys.argv[2]
    keys = set(sys.argv[3].split(','))
    stops = set(sys.argv[4].split(','))
    hpos = int(sys.argv[5]) if len(sys.argv) > 5 else None
    run(content, state, keys, stops, hpos=hpos)
