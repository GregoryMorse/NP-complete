"""Counter (Minsky) machine: builder DSL, assembler and interpreter.

Instructions after assembly (targets are instruction indices):
    ('INC', r, nxt)
    ('DEC', r, nz, z)     if r > 0: r -= 1, goto nz   else goto z
    ('BEEP', nxt)
JMP is a pseudo-instruction removed by the assembler.  There is no HALT:
Z_P never halts.
"""


class CM:
    def __init__(self):
        self.code = []          # raw: [op, args..., ] with label names / None
        self.labels = {}
        self._n = 0

    # ------------------------------------------------------------ builder
    def fresh(self, hint='L'):
        self._n += 1
        return f'_{hint}{self._n}'

    def label(self, name):
        assert name not in self.labels, name
        self.labels[name] = len(self.code)

    def inc(self, r):
        self.code.append(['INC', r, None])

    def dec(self, r, nz=None, z=None):
        self.code.append(['DEC', r, nz, z])

    def jmp(self, lbl):
        self.code.append(['JMP', lbl])

    def beep(self):
        self.code.append(['BEEP', None])

    # ------------------------------------------------------------- macros
    def clear(self, r):
        L = self.fresh('clr')
        self.label(L)
        self.dec(r, nz=L)

    def move(self, src, dsts):
        """dst += src for each dst (with multiplicity); src := 0."""
        L, E = self.fresh('mv'), self.fresh('mve')
        self.label(L)
        self.dec(src, z=E)
        for d in dsts:
            self.inc(d)
        self.jmp(L)
        self.label(E)

    def copy(self, src, dst, tmp='T'):
        self.move(src, [dst, tmp])
        self.move(tmp, [src])

    def pop(self, X, empty, B=None, T='T'):
        """X >= 1 is a rep.  If X == 1: X := 0, goto empty.  Otherwise
        B += X mod 2 (if B given) and X := X // 2."""
        L, OD, EV = self.fresh('pop'), self.fresh('od'), self.fresh('ev')
        self.label(L)
        self.dec(X, z=EV)
        self.dec(X, z=OD)
        self.inc(T)
        self.jmp(L)
        self.label(OD)
        self.dec(T, z=empty)
        self.inc(X)
        if B is not None:
            self.inc(B)
        self.label(EV)
        self.move(T, [X])

    # ----------------------------------------------------------- assemble
    def assemble(self):
        raw = self.code
        n = len(raw)
        lab = dict(self.labels)

        def tgt(i, t):
            if t is None:
                return i + 1
            return lab[t]

        # resolve to indices in raw space
        res = []
        for i, ins in enumerate(raw):
            op = ins[0]
            if op == 'INC':
                res.append(('INC', ins[1], tgt(i, ins[2])))
            elif op == 'DEC':
                res.append(('DEC', ins[1], tgt(i, ins[2]), tgt(i, ins[3])))
            elif op == 'JMP':
                res.append(('JMP', lab[ins[1]]))
            elif op == 'BEEP':
                res.append(('BEEP', tgt(i, ins[1])))
        # follow JMP chains

        def final(t):
            seen = set()
            while t < n and res[t][0] == 'JMP':
                if t in seen:
                    raise ValueError('jump cycle')
                seen.add(t)
                t = res[t][1]
            if t >= n:
                raise ValueError('falls off end of program')
            return t
        keep = [i for i in range(n) if res[i][0] != 'JMP']
        newidx = {old: k for k, old in enumerate(keep)}
        prog = []
        for i in keep:
            ins = res[i]
            if ins[0] == 'INC':
                prog.append(('INC', ins[1], newidx[final(ins[2])]))
            elif ins[0] == 'DEC':
                prog.append(('DEC', ins[1], newidx[final(ins[2])],
                             newidx[final(ins[3])]))
            else:
                prog.append(('BEEP', newidx[final(ins[1])]))
        entry = newidx[final(0)]
        labels = {k: newidx[final(v)] for k, v in lab.items()
                  if v < n and not k.startswith('_')}
        return Program(prog, entry, labels)


class Program:
    def __init__(self, code, entry, labels):
        self.code = code
        self.entry = entry
        self.labels = labels
        regs = []
        for ins in code:
            if ins[0] in ('INC', 'DEC') and ins[1] not in regs:
                regs.append(ins[1])
        self.regs = regs

    def __len__(self):
        return len(self.code)

    def stats(self):
        from collections import Counter
        c = Counter()
        for ins in self.code:
            if ins[0] in ('INC', 'DEC'):
                c[(ins[0], ins[1])] += 1
            else:
                c[(ins[0], None)] += 1
        return c

    def run(self, max_steps, on_beep=None, watch=None):
        """Interpret.  on_beep(step, regs) -> False to stop.
        watch: dict label -> callback(step, regs) called on arrival."""
        regs = {r: 0 for r in self.regs}
        pc = self.entry
        code = self.code
        watchpc = {}
        if watch:
            for k, f in watch.items():
                watchpc[self.labels[k]] = f
        step = 0
        while step < max_steps:
            if pc in watchpc:
                if watchpc[pc](step, regs) is False:
                    break
            ins = code[pc]
            op = ins[0]
            if op == 'INC':
                regs[ins[1]] += 1
                pc = ins[2]
            elif op == 'DEC':
                r = ins[1]
                if regs[r]:
                    regs[r] -= 1
                    pc = ins[2]
                else:
                    pc = ins[3]
            else:
                pc = ins[1]
                if on_beep and on_beep(step, regs) is False:
                    step += 1
                    break
            step += 1
        return step, regs, pc
