"""Counter-machine brute-force deciders for the NP-intermediate languages of
ref/np_intermediate.py.

emit(b, name) appends code that sets TR := [S in A] (TR is 0 on entry) while
preserving S and N = |s|.  Every other register it touches is 0 again on exit.
"""


class _K:
    """Small structured layer over the CM builder: fresh labels and
    temporaries, call/return through a counter flag."""

    def __init__(self, b, tag):
        self.b, self.tag, self._n = b, tag, 0

    def r(self, name):
        return f'{self.tag}_{name}'

    def lab(self, hint):
        return self.b.fresh(self.tag + hint)

    def copy(self, src, dst):
        self.b.copy(src, dst)

    def zero_test(self, r, nz, z):
        """goto z if r == 0, else goto nz (r unchanged)."""
        back = self.lab('zt')
        self.b.dec(r, nz=back, z=z)
        self.b.label(back)
        self.b.inc(r)
        self.b.jmp(nz)

    def halve(self, X, B=None):
        b = self.b
        T = self.r('hT')
        L, O, E = self.lab('hv'), self.lab('ho'), self.lab('he')
        b.label(L)
        b.dec(X, z=E)
        b.dec(X, z=O)
        b.inc(T)
        b.jmp(L)
        b.label(O)
        if B is not None:
            b.inc(B)
        b.label(E)
        b.move(T, [X])

    def mul_into(self, a, c, dst):
        """dst += a * c (a, c preserved)."""
        b = self.b
        t = self.r('mt')
        self.copy(a, t)
        L, D = self.lab('ml'), self.lab('md')
        b.label(L)
        b.dec(t, z=D)
        self.copy(c, dst)
        b.jmp(L)
        b.label(D)

    def eq(self, A, B, yes, no):
        """Consumes A and B; goto yes iff they were equal."""
        b = self.b
        L, A0, NA, NB = self.lab('eq'), self.lab('ea'), self.lab('na'), self.lab('nb')
        b.label(L)
        b.dec(A, z=A0)
        b.dec(B, z=NA)
        b.jmp(L)
        b.label(NA)
        b.clear(A)
        b.jmp(no)
        b.label(A0)
        b.dec(B, nz=NB, z=yes)
        b.label(NB)
        b.clear(B)
        b.jmp(no)

    def divmod(self, X, D, Q, Rm):
        """Q += X // D, Rm := X mod D (Rm 0 on entry); X consumed, D >= 1 kept."""
        b = self.b
        Dt = self.r('dt')
        L, IN, FULL, PART = self.lab('dm'), self.lab('di'), self.lab('df'), self.lab('dp')
        b.label(L)
        self.copy(D, Dt)
        b.label(IN)
        b.dec(Dt, z=FULL)
        b.dec(X, z=PART)
        b.inc(Rm)
        b.jmp(IN)
        b.label(FULL)
        b.inc(Q)
        b.clear(Rm)
        b.jmp(L)
        b.label(PART)
        b.clear(Dt)

    def subroutine(self, name, nsites, body):
        """Emit body() as a routine; return call(k) for call sites 0..nsites-1."""
        b = self.b
        flag = self.r('rf_' + name)
        entry, skip = self.lab(name), self.lab(name + 'skip')
        rets = [self.lab(f'{name}ret{k}') for k in range(nsites)]
        b.jmp(skip)
        b.label(entry)
        body()
        for k in range(nsites - 1):
            b.dec(flag, z=rets[k])
        b.jmp(rets[nsites - 1])
        b.label(skip)

        def call(k):
            for _ in range(k):
                b.inc(flag)
            b.jmp(entry)
            b.label(rets[k])
        return call


def emit_factor(b):
    k = _K(b, 'fa')
    r = k.r
    Nh, Par, U, K, Pw, Kr, Ar, D, Y, Dt, bit = map(r, (
        'Nh', 'Par', 'U', 'K', 'Pw', 'Kr', 'Ar', 'D', 'Y', 'Dt', 'bit'))
    REJ, ACC, DONE = k.lab('rej'), k.lab('acc'), k.lab('done')
    # m = N / 2 ; reject odd N and N = 0
    k.copy('N', Nh)
    k.halve(Nh, B=Par)
    EVEN, POS = k.lab('even'), k.lab('pos')
    b.dec(Par, z=EVEN)
    b.jmp(REJ)
    b.label(EVEN)
    k.zero_test(Nh, nz=POS, z=REJ)
    b.label(POS)
    # pop the last m bits of s into K (value k); U becomes rep of the first half
    k.copy('S', U)
    b.inc(Pw)
    POP, POPPED, NB = k.lab('pk'), k.lab('pkd'), k.lab('pnb')
    b.label(POP)
    b.dec(Nh, z=POPPED)
    b.pop(U, REJ, B=bit)                  # never empty: m < n
    b.dec(bit, z=NB)
    k.copy(Pw, K)
    b.label(NB)
    b.move(Pw, [r('Pw2'), r('Pw2')])
    b.move(r('Pw2'), [Pw])
    b.jmp(POP)
    b.label(POPPED)                       # U = 2^m + a, Pw = 2^m
    SUB, SD = k.lab('sub'), k.lab('sd')
    b.label(SUB)
    b.dec(Pw, z=SD)
    b.dec(U)
    b.jmp(SUB)
    b.label(SD)                           # U = a, K = k
    # trial division, d = 2, 3, ... while d <= k and d < a
    b.move(K, [Kr])
    b.dec(Kr, z=REJ)                      # Kr = k - d + 1
    k.copy(U, Ar)
    b.dec(Ar, z=REJ)
    b.dec(Ar, z=REJ)                      # Ar = a - d
    b.inc(D)
    b.inc(D)
    TRI, MODL, M1, INNER, NOTDIV = (k.lab(x) for x in ('tri', 'modl', 'm1', 'inner', 'nd'))
    b.label(TRI)
    b.dec(Kr, z=REJ)
    b.dec(Ar, z=REJ)
    k.copy(U, Y)
    b.label(MODL)
    b.dec(Y, nz=M1, z=ACC)                # remainder 0: d divides a
    b.label(M1)
    b.inc(Y)
    k.copy(D, Dt)
    b.label(INNER)
    b.dec(Dt, z=MODL)
    b.dec(Y, z=NOTDIV)
    b.jmp(INNER)
    b.label(NOTDIV)
    b.clear(Dt)
    b.inc(D)
    b.jmp(TRI)
    b.label(ACC)
    b.inc('TR')
    b.label(REJ)
    for x in (Nh, Par, U, K, Pw, Kr, Ar, D, Y, Dt, bit):
        b.clear(x)
    b.label(DONE)


def emit_gi(b):
    k = _K(b, 'gi')
    r = k.r
    REJ, ACC = k.lab('rej'), k.lab('acc')
    m, M2, Mm, F, Frem, I, J = map(r, ('m', 'M2', 'Mm', 'F', 'Frem', 'I', 'J'))
    DI, DV, BI, BV, FI, FJ, G = map(r, ('DI', 'DV', 'BI', 'BV', 'FI', 'FJ', 'G'))

    # ---- routines
    def digit():                           # DV := digit DI of F in base m; DI consumed
        Y, Q, Rm = r('dY'), r('dQ'), r('dR')
        k.copy(F, Y)
        L, D = k.lab('dgl'), k.lab('dgd')
        b.label(L)
        b.dec(DI, z=D)
        k.divmod(Y, m, Q, Rm)
        b.clear(Rm)
        b.move(Q, [Y])
        b.jmp(L)
        b.label(D)
        k.divmod(Y, m, Q, DV)
        b.clear(Q)
    call_digit = k.subroutine('digit', 2, digit)

    def bitr():                            # BV := bit BI of s (= bit BI of S); BI consumed
        Y = r('bY')
        k.copy('S', Y)
        L, D = k.lab('btl'), k.lab('btd')
        b.label(L)
        b.dec(BI, z=D)
        k.halve(Y)
        b.jmp(L)
        b.label(D)
        k.halve(Y, B=BV)
        b.clear(Y)
    call_bit = k.subroutine('bit', 2, bitr)

    # ---- m with 2 m^2 = N, else reject
    T2, Nc = r('T2'), r('Nc')
    ML, CMP, TEND, NEXTM, FOUND = (k.lab(x) for x in ('ml', 'cmp', 'tend', 'nm', 'found'))
    b.inc(m)
    b.label(ML)
    k.mul_into(m, m, T2)
    b.move(T2, [r('T2b'), r('T2b')])
    b.move(r('T2b'), [T2])
    k.copy('N', Nc)
    b.label(CMP)
    b.dec(T2, z=TEND)
    b.dec(Nc, z=REJ)                       # 2 m^2 > N
    b.jmp(CMP)
    b.label(TEND)
    b.dec(Nc, nz=NEXTM, z=FOUND)
    b.label(NEXTM)
    b.clear(Nc)
    b.inc(m)
    b.jmp(ML)
    b.label(FOUND)
    k.mul_into(m, m, M2)
    # Mm = m^m
    Pt, Pv = r('Pt'), r('Pv')
    b.inc(Mm)
    k.copy(m, Pt)
    PL, PD = k.lab('pl'), k.lab('pd')
    b.label(PL)
    b.dec(Pt, z=PD)
    b.move(Mm, [Pv])
    k.mul_into(Pv, m, Mm)
    b.clear(Pv)
    b.jmp(PL)
    b.label(PD)
    b.move(Mm, [Frem])
    # ---- for F in 0 .. m^m - 1, i, j in 0 .. m-1
    FL, IL, JL, IDONE, JDONE, FAIL = (k.lab(x) for x in ('fl', 'il', 'jl', 'id', 'jd', 'fail'))
    b.label(FL)
    b.dec(Frem, z=REJ)
    b.label(IL)
    A1, A2 = r('A1'), r('A2')
    k.copy(I, A1)
    k.copy(m, A2)
    INI = k.lab('ini')
    k.eq(A1, A2, yes=ACC, no=INI)          # all (i, j) passed: isomorphism found
    b.label(INI)
    b.label(JL)
    k.copy(J, A1)
    k.copy(m, A2)
    INJ = k.lab('inj')
    k.eq(A1, A2, yes=JDONE, no=INJ)
    b.label(INJ)
    # FI = f(i), FJ = f(j)
    k.copy(I, DI)
    call_digit(0)
    b.move(DV, [FI])
    k.copy(J, DI)
    call_digit(1)
    b.move(DV, [FJ])
    # injectivity: i != j  =>  f(i) != f(j)
    SAME, DIFF, OKINJ = k.lab('same'), k.lab('diff'), k.lab('okinj')
    k.copy(I, A1)
    k.copy(J, A2)
    k.eq(A1, A2, yes=OKINJ, no=DIFF)
    b.label(DIFF)
    k.copy(FI, A1)
    k.copy(FJ, A2)
    k.eq(A1, A2, yes=FAIL, no=OKINJ)
    b.label(OKINJ)
    # G[i][j] = bit m^2 + i m + j ; H[f(i)][f(j)] = bit f(i) m + f(j)
    k.copy(M2, BI)
    k.mul_into(I, m, BI)
    k.copy(J, BI)
    call_bit(0)
    b.move(BV, [G])
    k.mul_into(FI, m, BI)
    k.copy(FJ, BI)
    b.clear(FI)
    b.clear(FJ)
    call_bit(1)
    G1, G0, NEXTJ = k.lab('g1'), k.lab('g0'), k.lab('nj')
    b.dec(G, nz=G1, z=G0)
    b.label(G1)
    b.dec(BV, nz=NEXTJ, z=FAIL)
    b.label(G0)
    b.dec(BV, nz=FAIL, z=NEXTJ)
    b.label(NEXTJ)
    b.inc(J)
    b.jmp(JL)
    b.label(JDONE)
    b.clear(J)
    b.inc(I)
    b.jmp(IL)
    b.label(FAIL)
    for x in (FI, FJ, BV, G, I, J):
        b.clear(x)
    b.inc(F)
    b.jmp(FL)
    b.label(ACC)
    b.inc('TR')
    b.label(REJ)
    for x in (m, M2, Mm, F, Frem, I, J, T2, Nc):
        b.clear(x)



def emit_dlog(b):
    k = _K(b, 'dl')
    r = k.r
    REJ, ACC = k.lab('rej'), k.lab('acc')
    Nq, Par, U, V, Pw, bit = map(r, ('Nq', 'Par', 'U', 'V', 'Pw', 'bit'))
    m, p, g, h, kk, Y, Z, Q, Rm, D, Dt = map(r, ('m', 'p', 'g', 'h', 'k', 'Y', 'Z', 'Q', 'Rm',
                                                 'D', 'Dt'))
    # m = N / 4, N divisible by 4, m >= 1
    k.copy('N', Nq)
    for _ in range(2):
        k.halve(Nq, B=Par)
        OK = k.lab('p4')
        b.dec(Par, z=OK)
        b.jmp(REJ)
        b.label(OK)
    POS = k.lab('pos')
    k.zero_test(Nq, nz=POS, z=REJ)
    b.label(POS)
    b.move(Nq, [m])
    k.copy('S', U)

    def take():                         # V := next m bits of U (LSB first); Pw := 2^m
        cnt = r('cnt')
        k.copy(m, cnt)
        b.inc(Pw)
        L, D_, NB = k.lab('tk'), k.lab('tkd'), k.lab('tnb')
        b.label(L)
        b.dec(cnt, z=D_)
        b.pop(U, REJ, B=bit)            # never empty: 4m bits
        b.dec(bit, z=NB)
        k.copy(Pw, V)
        b.label(NB)
        b.move(Pw, [r('Pw2'), r('Pw2')])
        b.move(r('Pw2'), [Pw])
        b.jmp(L)
        b.label(D_)
    call_take = k.subroutine('take', 3, take)
    for site, dst in enumerate((kk, h, g)):
        call_take(site)
        b.move(V, [dst])
        b.clear(Pw)
    # U = 2^m + p
    b.inc(Pw)
    k.copy(m, r('cnt'))
    L, D_ = k.lab('pw'), k.lab('pwd')
    b.label(L)
    b.dec(r('cnt'), z=D_)
    b.move(Pw, [r('Pw2'), r('Pw2')])
    b.move(r('Pw2'), [Pw])
    b.jmp(L)
    b.label(D_)
    SUB, SD = k.lab('sub'), k.lab('sd')
    b.label(SUB)
    b.dec(Pw, z=SD)
    b.dec(U)
    b.jmp(SUB)
    b.label(SD)
    b.move(U, [p])
    # p prime: p >= 2 and no d in [2, p-1] divides p
    Ar = r('Ar')
    k.copy(p, Ar)
    b.dec(Ar, z=REJ)
    b.dec(Ar, z=REJ)                    # Ar = p - 2 = number of trial divisors
    b.inc(D)
    b.inc(D)
    TRI, MODL, M1, INNER, NOTDIV, PRIME = (k.lab(x) for x in ('tri', 'modl', 'm1', 'in', 'nd', 'pr'))
    b.label(TRI)
    b.dec(Ar, z=PRIME)
    k.copy(p, Y)
    b.label(MODL)
    b.dec(Y, nz=M1, z=REJ)              # d divides p: composite
    b.label(M1)
    b.inc(Y)
    k.copy(D, Dt)
    b.label(INNER)
    b.dec(Dt, z=MODL)
    b.dec(Y, z=NOTDIV)
    b.jmp(INNER)
    b.label(NOTDIV)
    b.clear(Dt)
    b.inc(D)
    b.jmp(TRI)
    b.label(PRIME)
    b.clear(D)
    # h := h mod p ; y := 1 ; for x = 0..k: if y == h accept ; y := y g mod p
    k.divmod(h, p, Q, Rm)
    b.clear(Q)
    b.move(Rm, [h])
    b.inc(Y)
    b.inc(kk)
    XL, NE = k.lab('xl'), k.lab('ne')
    b.label(XL)
    b.dec(kk, z=REJ)
    A1, A2 = r('A1'), r('A2')
    k.copy(Y, A1)
    k.copy(h, A2)
    k.eq(A1, A2, yes=ACC, no=NE)
    b.label(NE)
    k.mul_into(Y, g, Z)
    b.clear(Y)
    k.divmod(Z, p, Q, Y)
    b.clear(Q)
    b.jmp(XL)
    b.label(ACC)
    b.inc('TR')
    b.label(REJ)
    for x in (Nq, Par, U, V, Pw, bit, m, p, g, h, kk, Y, Z, Q, Rm, D, Dt, Ar, r('cnt')):
        b.clear(x)


EMIT = {'factor': emit_factor, 'gi': emit_gi, 'dlog': emit_dlog}


def harness(name):
    """Test program: S = 1, 2, ...; beep iff S in A (exercises emit alone)."""
    from cm import CM
    b = CM()
    b.inc('S')
    b.label('loop')
    b.copy('S', 'U')
    L, D = b.fresh('len'), b.fresh('lend')
    b.label(L)
    b.pop('U', D)
    b.inc('N')
    b.jmp(L)
    b.label(D)
    EMIT[name](b)
    b.dec('TR', z='nob')
    b.beep()
    b.label('nob')
    b.clear('N')
    b.inc('S')
    b.jmp('loop')
    return b
