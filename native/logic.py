"""4-symbol 'logical' machines (symbols B M 0 1) and a simulator."""
SYMS = 'BM01'


class LTM:
    def __init__(self, start):
        self.d = {}
        self.start = start
        self.beep = None

    def t(self, q, syms, w, m, n):
        for s in syms:
            assert (q, s) not in self.d, (q, s)
            self.d[(q, s)] = (s if w == '.' else w, m, n)

    def states(self):
        qs = {q for q, _ in self.d}
        missing = {n for (_, _, n) in self.d.values()} - qs
        assert not missing, missing
        return [self.start] + sorted(qs - {self.start})


def run(m, steps, on_beep=None):
    tape, h, q = {}, 0, m.start
    for i in range(steps):
        tr = m.d.get((q, tape.get(h, 'B')))
        if tr is None:
            return 'halt', q, tape, h, i
        tape[h], mv, q = tr
        h += 1 if mv == 'R' else -1
        if q == m.beep and on_beep and not on_beep(tape, h):
            return 'stop', q, tape, h, i
    return 'steps', q, tape, h, steps


def show(tape, h=None):
    lo, hi = min(tape), max(tape)
    return ''.join(('[' if i == h else '') + tape.get(i, 'B') for i in range(lo, hi + 1))
