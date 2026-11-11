import sys
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import gen_polyseg_gen as gen
out = []


def add(*a, **k):
    txt, ks = gen.seg(*a, **k)
    out.append(txt)
    print(a[0], ks)


V = {'Kl': 'bits', 'Kr': 'bits', 'a': 'bits', 's': 'bits', 'T': 'O13'}
add('blkStart', 'BLK starts: `M` at the end, back to the first bit of `s`.', V,
    ('GRB', ['Kl', 1, 'Kr', 1, 'a', 1, 's', 1, 'T'], [], False), 'COPY')
open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), 'out', 'segs1.lean'), 'w').write('\n'.join(out))
