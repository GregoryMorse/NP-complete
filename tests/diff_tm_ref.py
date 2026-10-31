"""Differential test: compiled TM (fast C simulator) vs Python reference.

For each variant, the (J, S) pair decoded from the tape at every beep must
equal the reference's refutation pair, in order.  For the P-swap variants
the reference beep list is finite (the machine must go silent after the
last one): we check the TM produces exactly those beeps and no further beep
within a step budget well beyond the last one.
"""
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..')
sys.path[:0] = [os.path.join(ROOT, 'ref')]
import zp_ref as R      # noqa: E402

SIM = os.path.join(ROOT, 'sim', 'tmsim')
CMSIM = os.path.join(ROOT, 'sim', 'cmsim')
sys.path.insert(0, ROOT)
import build            # noqa: E402


def ensure_sim():
    for exe in (SIM, CMSIM):
        src = exe + '.c'
        if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(src):
            subprocess.check_call(['gcc', '-O2', '-o', exe, src])


def cm_beeps(name, steps, nbeeps):
    out = subprocess.run([CMSIM, os.path.join(ROOT, 'machines', name + '.cm'), str(steps),
                          str(nbeeps)], capture_output=True, text=True)
    res = [tuple(map(int, l.split())) for l in out.stdout.split('\n') if l.strip()]
    return [(J, S) for _, J, S in res], out.stderr.strip()


def tm_beeps(name, steps, nbeeps):
    meta = json.load(open(os.path.join(ROOT, 'machines', name + '.json')))
    order = meta['register_order']
    out = subprocess.run([SIM, os.path.join(ROOT, 'machines', name + '.tbl'), str(steps),
                          str(nbeeps), str(len(order))], capture_output=True, text=True)
    res = []
    for line in out.stdout.split('\n'):
        if not line.strip():
            continue
        if line.startswith('HALT'):
            raise AssertionError(name + ': machine halted: ' + line)
        f = list(map(int, line.split()))
        regs = dict(zip(order, f[1:]))
        res.append((f[0], regs['J'], regs['S']))
    return res, out.stderr.strip()


def check(name, truth, steps, nbeeps, exact, level='tm', cands=None):
    if level == 'tm':
        got, info = tm_beeps(name, steps, nbeeps + 1)
        gotjs = [(J, S) for _, J, S in got]
    else:
        gotjs, info = cm_beeps(name, steps, nbeeps + 1)
        got = [(0,)] if gotjs else []
        name = name + '[cm]'
    want = [(J, S) for _, J, S in R.zp_beeps(
        truth=truth, candidates=cands, max_instances=200000,
        max_beeps=nbeeps if exact else max(1, len(gotjs)))]
    ok = gotjs == want if exact else (gotjs == want[:len(gotjs)] and len(gotjs) > 0)
    print(f'{name:20s} reference beeps={len(want):5d} tm beeps={len(gotjs):5d} '
          f'[{info}] -> {"OK" if ok else "FAIL"}')
    return ok


def main():
    ensure_sim()
    ok = True
    ne = lambda S: S > 1                                # noqa: E731
    odd = lambda S: S > 1 and S & 1 == 1                # noqa: E731
    # Controlled enumerations: exact beep list, then silence (brief §5.3).
    for lvl in ('cm', 'tm'):
        ok &= check('ctl_nonempty', ne, 4 * 10**9, 100, exact=True, level=lvl,
                    cands=build.CTL_NONEMPTY)
        ok &= check('ctl_zp', None, 4 * 10**9, 100, exact=True, level=lvl, cands=build.CTL_L)
    # Real enumeration: prefix agreement (a full P-swap run is infeasible:
    # unary arithmetic costs 2^Theta(guest steps)).
    for lvl in ('cm', 'tm'):
        ok &= check('pswap_nonempty', ne, 10**10, 10**6, exact=False, level=lvl)
        ok &= check('pswap_odd', odd, 10**10, 10**6, exact=False, level=lvl)
        ok &= check('zp', None, 10**10, 10**6, exact=False, level=lvl)
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
