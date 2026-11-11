import re
p = '/home/user/np-complete/.claude/worktrees/agent-a63be367c1b1600e3/formal/ZP/PairPoly.lean'
t = open(p).read()
lines = t.split('\n')
drop = {'sinc0', 'sinc1', 'blkDecStep', 'blkDecLast', 'blkCopy', 'decFuel'}
starts = [k for k, l in enumerate(lines) if re.match(r'(theorem |def |/--|/-!|macro |end |namespace |open )', l)]
chunks = []
k = 0
while k < len(starts):
    s = starts[k]
    e = starts[k + 1] if k + 1 < len(starts) else len(lines)
    if lines[s].startswith('/--') and k + 1 < len(starts) and re.match(r'(theorem |def )', lines[starts[k + 1]]) and starts[k + 1] - s <= 3:
        e = starts[k + 2] if k + 2 < len(starts) else len(lines)
        k += 1
    chunks.append((s, e))
    k += 1
res = lines[:starts[0]]
for s, e in chunks:
    ch = lines[s:e]
    name = None
    for l in ch:
        m = re.match(r'(theorem|def) (\S+)', l)
        if m:
            name = m.group(2)
            break
    if name in drop:
        continue
    res += ch
t = '\n'.join(res)
g = ''
for f in ['segs1', 'segs2', 'segs3', 'segs4']:
    g += open('/tmp/claude-0/sp/%s.lean' % f).read() + '\n'
i = t.index('/-! ## Small facts -/')
t = t[:i] + '/-! ## Generated segments (poly layout `M_g rev(K) M_1 a M_a s`) -/\n\n' + g + '\n' + t[i:]
open(p, 'w').write(t)
