"""Native machines (native/): the logical machines and the compiled 2-symbol
machines must beep exactly at the refutations predicted by the references.

  zp_native   P = NP   ref/zp2_ref.py
  zpp_native  P = PP   ref/zpp_ref.py
  zps_native  P = PSPACE  ref/zps_ref.py
  zconp_native  NP = coNP  ref/zconp_ref.py
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
import logic        # noqa: E402
import test_logic   # noqa: E402
import check2       # noqa: E402
import final        # noqa: E402
import inst         # noqa: E402
import zp2          # noqa: E402
import zpp          # noqa: E402
import zps          # noqa: E402
import zconp        # noqa: E402
import cinst        # noqa: E402

MACHINES = {
    'zp_native': (zp2, zp2_ref.zp_beeps, None),
    'zpp_native': (zpp, zpp_ref.zp_beeps, zpp_ref.in_LPP),
    'zps_native': (zps, zps_ref.zp_beeps, zps_ref.in_LPS),
    'zconp_native': (zconp, zconp_ref.zp_beeps, None),
}
# beyond 13 beeps the NP = coNP reference needs exponentially many runs
MAXB = {'zconp_native': 13}


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
        k = min(n, MAXB.get(name, n))
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
    test_compiled()
    print('compiled ok')
