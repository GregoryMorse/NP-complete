# State-count history

Every row is reproducible from the commit that introduced it (`python3 build.py`).

| states | change |
|---:|---|
| 2821 | first complete machine: TM-guest with w,d,unary entries, E-anchored INC/DEC templates, minimization |
| 2257 | offset machines with unary entries e = 4k+2d+w (one pop site), cleanup once at `run` entry |
| 1817 | two-ended navigation (walk from the left end when cheaper) |
| 1710 | manual register sharing, annealed layout |
| 1662 | native O(1) transfer between adjacent registers |
| 1406 | must-zero analysis + register coalescing (per-site temporaries, 41 → 17 registers) jointly annealed with the layout |
| **1371** | peephole: step left straight into the successor's walk instead of detouring through E |

Twin-prime beeper (same backend): 265.

## Where the states go (1504 before minimization, 1371 after)
| part | states | share |
|---|---:|---:|
| walking to registers (one state per block passed) | 650 | 43% |
| DEC bodies (zero test, hole propagation, return scan) | 693 | 46% |
| INC bodies (carry shift) | 106 | 7% |
| native adjacent moves | 21 | 1% |
| initialisation (2k−1 for k = 17 registers) | 33 | 2% |
| beep | 1 | – |

## Next golfing steps (not done)
1. A simulating architecture instead of arithmetic: keep the guest tape, code and
   counters directly on the host tape in binary, with a small fixed interpreter. This is
   how hand-built universal machines are made small, and is expected to win by a large factor.
2. Cheaper DEC: the 10-state body dominates. Options are carry-shift variants with
   shared continuations, or representations with slack cells.
3. Superoptimization of repeated fragments (brief §7.3), with the beep state excluded.
