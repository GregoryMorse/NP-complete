import sys
W = '/home/user/np-complete/.claude/worktrees/agent-a1d5c3c256203d737'
sys.path[:0] = [W + '/native', W + '/ref', W + '/formal/scripts']
import zlp
m = zlp.build()


def sim(m, tape, h, q, until, limit=10**7, log=None):
    """tape: dict pos->sym; run until state in until (set) or limit; returns (q,h,tape,steps)"""
    k = 0
    while k < limit:
        if q in until and k > 0:
            return q, h, tape, k
        tr = m.d.get((q, tape.get(h, 'B')))
        if tr is None:
            return 'HALT:' + q, h, tape, k
        tape[h], mv, q = tr
        h += 1 if mv == 'R' else -1
        k += 1
        if log:
            log(q, h, tape, k)
    return q, h, tape, k


def show(tape, h, lo=None, hi=None):
    lo = min(tape) if lo is None else lo
    hi = max(tape) if hi is None else hi
    return ''.join(('[' if i == h else '') + tape.get(i, 'B') + (']' if i == h else '') for i in range(lo, hi + 1))


def mk(s, off=0):
    return {i + off: c for i, c in enumerate(s) if c != '_'}


if __name__ == '__main__':
    q, h, tape, k = sim(m, {}, 0, m.start, {'TW'})
    print(q, h, k, show(tape, h))
