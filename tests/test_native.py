"""Native machines (native/): the logical machines and the compiled 2-symbol
machines must beep exactly at the refutations predicted by the references.

  zp_native   P = NP   ref/zp2_ref.py
  zpp_native  P = PP   ref/zpp_ref.py
  zps_native  P = PSPACE  ref/zps_ref.py
  zconp_native  NP = coNP  ref/zconp_ref.py
  zfactor_native  factoring in P  ref/zfac_ref.py
  zdlog_native  discrete log mod primes in P  ref/zdl_ref.py
  zgi_native  graph isomorphism in P  ref/zgi_ref.py
  zmul_native  linear-time multiplication  ref/zmul_ref.py
  zntt_native  linear-size NTT circuits  ref/zntt_ref.py
"""
import os
import subprocess
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..')
sys.path[:0] = [os.path.join(ROOT, 'native'), os.path.join(ROOT, 'ref')]
import zp2_ref      # noqa: E402
import zpp_ref      # noqa: E402
import zps_ref      # noqa: E402
import zconp_ref    # noqa: E402
import zfac_ref     # noqa: E402
import zdl_ref      # noqa: E402
import zgi_ref      # noqa: E402
import zmul_ref     # noqa: E402
import zntt_ref     # noqa: E402
import logic        # noqa: E402
import test_logic   # noqa: E402
import check2       # noqa: E402
import final        # noqa: E402
import inst         # noqa: E402
import zp2          # noqa: E402
import zpp          # noqa: E402
import zps          # noqa: E402
import zconp        # noqa: E402
import zfac         # noqa: E402
import zdl          # noqa: E402
import zgi          # noqa: E402
import zmul         # noqa: E402
import zntt         # noqa: E402
import cinst        # noqa: E402

MACHINES = {
    'zp_native': (zp2, zp2_ref.zp_beeps, None),
    'zpp_native': (zpp, zpp_ref.zp_beeps, zpp_ref.in_LPP),
    'zps_native': (zps, zps_ref.zp_beeps, zps_ref.in_LPS),
    'zconp_native': (zconp, zconp_ref.zp_beeps, None),
    'zfactor_native': (zfac, zfac_ref.zp_beeps, None),
    'zdlog_native': (zdl, zdl_ref.zp_beeps, None),
    'zgi_native': (zgi, zgi_ref.zp_beeps, None),
    'zmul_native': (zmul, zmul_ref.zp_beeps, None),
    'zntt_native': (zntt, lambda max_beeps: ((b, '1' * c, '1' * n) for b, c, n in
                                            zntt_ref.zp_beeps(max_beeps)), None),
}
# the NTT machine beeps with (C, Nn) in tape fields 3 and 4
FIELDS = {'zntt_native': (3, 4)}
# the second NTT refutation (c = 2) is far out of reach
MAXB_NTT = {'zntt_native': 2}
# beyond 13 beeps the NP = coNP reference needs exponentially many runs
MAXB = {'zconp_native': 13}
# the truth-routine machines examine ~60 instances per candidate: keep CI short
MAXB.update({'zfactor_native': 8, 'zdlog_native': 8, 'zgi_native': 12, 'zmul_native': 12})
# the logical machines of the native truth routines are slow to simulate in Python
MAXB.update(MAXB_NTT)
LOGICAL_MAXB = {'zfactor_native': 4, 'zdlog_native': 4, 'zmul_native': 6}


def want(beeps, n):
    return [(J, s) for _, J, s in beeps(max_beeps=n)]


def logical_beeps(mod, n, steps=10**8, fields=(1, 2)):
    out = []

    def cb(tape, h):
        out.append(test_logic.decode(tape, fields))
        return len(out) < n
    logic.run(mod.build(), steps, cb)
    return out


def load_tbl(path):
    rows = open(path).read().split('\n')
    ns, beep = map(int, rows[0].split())
    table = []
    for r in rows[1:ns + 1]:
        v = list(map(int, r.split()))
        table.append([None if v[3 * a + 2] < 0 else (v[3 * a], 'R' if v[3 * a + 1] else 'L', v[3 * a + 2])
                      for a in (0, 1)])
    return table, beep


def test_logical(n=12):
    for name, (mod, beeps, _) in MACHINES.items():
        k = min(n, MAXB.get(name, n), LOGICAL_MAXB.get(name, n))
        got = logical_beeps(mod, k, fields=FIELDS.get(name, (1, 2)))
        assert got == want(beeps, k), (name, got)


def test_pp_instances():
    # s where 'some certificate accepts' and 'at least half accept' differ
    m = zpp.build()
    for J, s in (('', '111001010'), ('', '0100101'), ('', '001011'), ('1', '111001010')):
        assert inst.instance(m, J, s) == zp2_ref.correct(J, s, zpp_ref.in_LPP), (J, s)


def test_ps_instances():
    # s where 'some certificate accepts' and the quantifier game differ
    m = zps.build()
    for J in ('', '1'):
        for s in ('00110', '10001', '1011010'):
            assert inst.instance(m, J, s) == zp2_ref.correct(J, s, zps_ref.in_LPS), (J, s)


def test_conp_instances():
    # pairs whose depth-first certificate search takes several runs
    m = zconp.build()
    for J, s in (('010101', '1110'), ('01', '1101'), ('0011011', '1110'), ('110001', '1110'),
                 ('100', '110'), ('1', '110'), ('', '1110'), ('0010', '0'), ('0010', '01')):
        assert cinst.instance(m, J, s) == zconp_ref.correct(J, s), (J, s)


def enc_numbers(*xs):
    """Instance string for the numbers xs (zfac_ref encoding)."""
    return '0'.join(''.join('1' + b for b in (bin(x)[2:] if x else '')) for x in xs)


def test_factor_instances():
    # (k, a): divisor found / none up to k / prime a / a = 0
    m = zfac.build()
    for k, a in ((5, 35), (4, 35), (6, 13), (12, 13), (3, 0), (1, 6), (9, 9)):
        s = enc_numbers(k, a)
        assert inst.instance_ni(m, '', s) == zfac_ref.correct('', s), (k, a)


def test_dlog_instances():
    # (k, h, g, p): log found / beyond k / composite p / h >= p
    m = zdl.build()
    for q in ((6, 3, 3, 7), (4, 3, 3, 7), (5, 1, 2, 9), (3, 9, 2, 7), (2, 0, 0, 5), (10, 4, 2, 11)):
        s = enc_numbers(*q)
        assert inst.instance_ni(m, '', s) == zdl_ref.correct('', s), q


def enc_graphs(m, X, H):
    """Instance string for (m, X, H) (zgi_ref encoding)."""
    return '0'.join('1' * v for v in reversed([m] + list(X) + [0] + list(H)))


def test_gi_instances():
    # path / out-star / one edge / extra edge / loop / repeated edge / odd X / 2-cycle
    m = zgi.build()
    for q in ((3, (1, 2, 2, 3), (1, 1, 1, 2, 1, 1, 1, 2, 1)),
              (3, (1, 2, 2, 3), (1, 2, 2, 1, 1, 1, 1, 1, 1)),
              (3, (1, 2), (1, 1, 1, 1, 1, 1, 1, 2, 1)),
              (3, (1, 2), (1, 2, 1, 1, 1, 1, 1, 2, 1)),
              (2, (1, 1), (1, 1, 1, 3)),
              (2, (1, 2, 1, 2), (1, 2, 2, 1)),
              (2, (1, 2, 1), (1, 2, 1, 1)),
              (3, (1, 1, 2, 3, 3, 2), (1, 2, 1, 1, 1, 1, 1, 1, 2)),
              (3, (1, 2, 2, 1), (1, 1, 1, 1, 1, 2, 1, 2, 1))):
        s = enc_graphs(*q)
        assert inst.instance_ni(m, '', s) == zgi_ref.correct('', s), q


def tm_code(states):
    """zmul guest code for a machine given as states[q] = 3 actions (read blank, 0,
    1): ('W', w, d, q2) or ('H',) (proper halt).  State q starts at entry 5q + 1."""
    N = 5 * len(states) + 1
    ents = [('0', '0', 1)] * N
    for q, acts in enumerate(states):
        P = 5 * q + 1
        for i, a in enumerate(acts):
            ents[P + i] = ('1', '0', 0) if a[0] == 'H' else (a[1], a[2], (5 * (a[3] - q) - i - 2) % N)
    return ''.join(f'{w}{d}' + '1' * k + '0' for w, d, k in ents)[:-1][::-1]


def test_mul_instances():
    m = zmul.build()
    cases = [  # random codes with switches that move cells
        ('100001011', '01100'), ('100001011', '110001'), ('010110100', '1011'),
        ('100100001', '0101'), ('01010011', '110110'), ('11001011', '110010')]
    writer = tm_code([[('W', b, '1', q + 1)] * 3 for q, b in enumerate('1111')] + [[('H',)] * 3])
    for s in (enc_numbers(1, 3), enc_numbers(3, 1), enc_numbers(3), enc_numbers(2, 1), enc_numbers(3, 1, 5)):
        cases.append((writer, s))   # writes 3 = '1111'
    want = [zmul_ref.correct(J, s) for J, s in cases]
    assert True in want and False in want
    for (J, s), w in zip(cases, want):
        assert inst.instance_ni(m, J, s) == w, (J, s)


def ntt_tape(c, n, recs):
    """zntt tape before the evaluation of recs = [(u, b)] (u None: none)."""
    p = zntt_ref.prime(n)
    W = c * n + 2

    def fld(v, w):
        return '1' * v + '0' * (w - v)
    s = '1' * W + 'M' + '1' * p + 'M111M' + '1' * c + 'M' + '1' * n
    for j, (u, b) in enumerate(recs):
        s += 'MM0' + ('1' if j >= c * n - n else '0') + '0M' + fld(1, p) + 'M' + fld(1, p)
        s += 'M' + fld(b + 1, p) + 'M' + fld(1 if u is None else u + 3, j + 2)
    return s


def ntt_instance(m, c, n, recs, steps=10**9):
    s = ntt_tape(c, n, recs)
    tape, h, q = dict(enumerate(s)), len(s) - 1, 'WI0'
    for _ in range(steps):
        tape[h], mv, q = m.d[(q, tape.get(h, 'B'))]
        h += 1 if mv == 'R' else -1
        if q in ('ODL', 'SU0'):
            return q == 'SU0'
    raise RuntimeError('step limit')


def test_ntt_instances():
    # DFT_2 with c = 3; DFT_3 with c = 6 (roots 1, 2, 4 mod 7); wrong or repeated roots
    m = zntt.build()
    d2 = [(None, 0), (0, 1), (1, 1), (0, 2), (2, 1), (3, 2)]
    d3 = [(None, 0), (0, 6), (1, 6), (2, 0), (2, 6), (0, 1), (1, 1), (2, 1), (7, 6), (1, 4),
          (2, 5), (10, 6), (1, 4), (2, 3), (13, 6), (7, 1), (10, 2), (13, 4)]
    cases = [(3, 2, d2), (6, 3, d3), (3, 2, d2[:5] + [(3, 1)]), (3, 2, d2[:5] + [(2, 2)])]
    for j, b in ((15, 2), (16, 1), (17, 2), (9, 3)):
        cases.append((6, 3, d3[:j] + [(d3[j][0], b)] + d3[j + 1:]))
    want = [zntt_ref.evaluate(n, zntt_ref.prime(n), r) for c, n, r in cases]
    assert want[:2] == [True, True] and not any(want[2:]), want
    # roots of x^3 = 6 mod 7 in the order 6, 3, 5; DFT_2 with the roots in the order 2, 1
    e3 = [(None, 0), (0, 6), (1, 6), (2, 0), (2, 6), (0, 6), (1, 1), (2, 6), (7, 6), (1, 6),
          (2, 5), (10, 6), (1, 6), (2, 6), (13, 6), (7, 6), (10, 3), (13, 5)]
    e2 = [(None, 0), (0, 2), (1, 2), (0, 2), (1, 1), (4, 2), (1, 2), (6, 2), (4, 2), (6, 1)]
    cases += [(6, 3, e3), (5, 2, e2)]
    want += [True, True]
    assert [zntt_ref.evaluate(n, zntt_ref.prime(n), r) for c, n, r in cases[-2:]] == [True, True]
    for (c, n, r), w in zip(cases, want):
        assert ntt_instance(m, c, n, r) == w, (c, n, r)


def test_decider_clock():
    """The decider fuel of zp2 lasts exactly zp2_ref.clock(J, s) guest steps: a guest
    that never halts makes exactly that many successful fuel decrements."""
    m = zp2.build()
    for J, s in [('111', ''), ('1111', ''), ('111', '0'), ('111', '01')]:
        w = ['M'] + list(J) + ['M'] + list(s)
        tape = dict(enumerate(w))
        h, q, prev, dec = len(w), 'GRB', None, 0
        while q not in ('DP40', 'DP41'):
            if q in ('DP10', 'DP11') and prev not in ('DP10', 'DP11'):
                dec = 0                     # a verifier run ended
            if q == 'FBACK' and prev != 'FBACK':
                dec += 1
            if q == 'EXH' and prev != 'EXH':
                last = dec
            prev = q
            tape[h], mv, q = m.d[(q, tape.get(h, 'B'))]
            h += 1 if mv == 'R' else -1
        assert last == zp2_ref.clock(J, s), (J, s, last, zp2_ref.clock(J, s))


def test_compiled(n=None):
    n = n or int(os.environ.get('NATIVE_BEEPS', '40'))
    subprocess.check_call(['gcc', '-O2', '-o', os.path.join(ROOT, 'native', 'psim'),
                           os.path.join(ROOT, 'native', 'psim.c')])
    for name, (_, beeps, _) in MACHINES.items():
        k = min(n, MAXB.get(name, n))
        table, beep = load_tbl(os.path.join(ROOT, 'machines', name + '.tbl'))
        got = check2.beeps(table, beep, final.ENC, k, fields=FIELDS.get(name, (1, 2)))
        assert got == want(beeps, k), (name, got[-3:], len(got))


if __name__ == '__main__':
    test_logical()
    print('logical ok')
    test_decider_clock()
    print('decider clock ok')
    test_pp_instances()
    print('pp instances ok')
    test_ps_instances()
    print('ps instances ok')
    test_conp_instances()
    print('conp instances ok')
    test_factor_instances()
    test_dlog_instances()
    test_mul_instances()
    test_ntt_instances()
    print('factor/dlog instances ok')
    test_compiled()
    print('compiled ok')
