import sys
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import gen_polyseg_gen as gen
out = []


def add(*a, **k):
    txt, ks = gen.seg(*a, **k)
    out.append(txt)
    print(a[0], ks)


V = {'Kr': 'bits', 'a': 'bits', 's': 'bits', 'C': 'T3'}
add('blkVer', 'Verifier fuel block done: write `H`, go to the guest source `C`.', V,
    ('COPY', [1, 'Kr', 1, 'a', 1, 's'], [1, 3, 'C', 1, 1, ('s', 3)], False), 'GC')
open('/tmp/claude-0/sp/segs2.lean', 'w').write('\n'.join(out))
