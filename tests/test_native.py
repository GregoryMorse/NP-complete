"""Z_P v2 (native/): the logical machine and the compiled 2-symbol machine
must beep exactly at the refutations predicted by ref/zp2_ref.py."""
import os
import subprocess
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..')
sys.path[:0] = [os.path.join(ROOT, 'native'), os.path.join(ROOT, 'ref')]
import zp2_ref      # noqa: E402
import test_logic   # noqa: E402
import check2       # noqa: E402
import final        # noqa: E402


def want(n):
    return [(J, s) for _, J, s in zp2_ref.zp_beeps(max_beeps=n)]


def test_logical(n=12):
    got, _ = test_logic.beeps(n)
    assert got == want(n), got


def load_tbl(path):
    rows = open(path).read().split('\n')
    ns, beep = map(int, rows[0].split())
    table = []
    for r in rows[1:ns + 1]:
        v = list(map(int, r.split()))
        table.append([None if v[3 * a + 2] < 0 else (v[3 * a], 'R' if v[3 * a + 1] else 'L', v[3 * a + 2])
                      for a in (0, 1)])
    return table, beep


def test_compiled(n=None):
    n = n or int(os.environ.get('NATIVE_BEEPS', '40'))
    subprocess.check_call(['gcc', '-O2', '-o', os.path.join(ROOT, 'native', 'psim'),
                           os.path.join(ROOT, 'native', 'psim.c')])
    table, beep = load_tbl(os.path.join(ROOT, 'machines', 'zp_native.tbl'))
    got = check2.beeps(table, beep, final.ENC, n)
    assert got == want(n), (got[-3:], len(got))


if __name__ == '__main__':
    test_logical()
    print('logical ok')
    test_compiled()
    print('compiled ok')
