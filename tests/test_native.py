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
}
# beyond 13 beeps the NP = coNP reference needs exponentially many runs
MAXB = {'zconp_native': 13}
# the truth-routine machines examine ~60 instances per candidate: keep CI short
MAXB.update({'zfactor_native': 8, 'zdlog_native': 8, 'zgi_native': 12, 'zmul_native': 12})
# the logical machines of the native truth routines are slow to simulate in Python
LOGICAL_MAXB = {'zfactor_native': 4, 'zdlog_native': 4, 'zmul_native': 6}


def want(beeps, n):
    return [(J, s) for _, J, s in beeps(max_beeps=n)]


def logical_beeps(mod, n, steps=10**8):
    out = []

    def cb(tape, h):
        out.append(test_logic.decode(tape))
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
        got = logical_beeps(mod, k)
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


def test_compiled(n=None):
    n = n or int(os.environ.get('NATIVE_BEEPS', '40'))
    subprocess.check_call(['gcc', '-O2', '-o', os.path.join(ROOT, 'native', 'psim'),
                           os.path.join(ROOT, 'native', 'psim.c')])
    for name, (_, beeps, _) in MACHINES.items():
        k = min(n, MAXB.get(name, n))
        table, beep = load_tbl(os.path.join(ROOT, 'machines', name + '.tbl'))
        got = check2.beeps(table, beep, final.ENC, k)
        assert got == want(beeps, k), (name, got[-3:], len(got))


if __name__ == '__main__':
    test_logical()
    print('logical ok')
    test_pp_instances()
    print('pp instances ok')
    test_ps_instances()
    print('ps instances ok')
    test_conp_instances()
    print('conp instances ok')
    test_factor_instances()
    test_dlog_instances()
    test_mul_instances()
    print('factor/dlog instances ok')
    test_compiled()
    print('compiled ok')
