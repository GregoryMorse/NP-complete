"""Insert a generated segment file into ZP/PairPoly.lean before the marker.

usage: gen_polyseg_insert.py out/segsN.lean 'Section title'
"""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
P = os.path.join(HERE, '..', 'ZP', 'PairPoly.lean')
t = open(P).read()
g = open(os.path.join(HERE, sys.argv[1])).read()
i = t.index('/-! ## Small facts -/')
t = t[:i] + '/-! ## ' + sys.argv[2] + ' -/\n\n' + g + '\n\n' + t[i:]
open(P, 'w').write(t)
