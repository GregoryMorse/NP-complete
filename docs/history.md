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

## Is 1371 near the floor of this design? Yes.
More layout search finds 1358–1374 states (60 000 annealing iterations, three seeds), so the
current pipeline (counter program → unary-register TM) has saturated. The cost is
structural: ~177 counter instructions at ~7.7 states each. Every instruction owns its
own walk to its register and its own DEC body, because a TM state cannot be shared
between call sites unless the return address lives on the tape.

## Route to ~750, and why ~200 needs a different idea
1. **Interpreter architecture (target ~500–750).** A fixed universal interpreter for a
   *macro* register machine, with COPY, MOVE, HALVE/POP, ZERO-TEST and JUMP as primitives,
   plus a loader that writes the program onto the tape. Z_P would be roughly 50 macro operations
   (enumerate, length, pow, certificate sweep, one guest step), roughly 600–800 program
   bits. At 1–2 bits per loader state that is 300–600 states, plus an interpreter of
   ~150–250 states. Navigation is paid once, in the interpreter, not per instruction.
   (These figures are estimates and are not yet built.)
2. **A cheaper guest.** About half the counter program is the offset-machine interpreter.
   A guest model whose step is one or two arithmetic primitives, with polynomial-time
   simulation of TMs (needed for Lemma 1), shrinks both the program and the proofs. The
   proof obligations (NP-hardness with a fixed input encoding, Lemma 1(a)) must be
   redone for any new guest.
3. **~200 states** would need both of the above plus hand-golfed interpreter code. The
   Σ₂ program is inherently bigger than a Π₁ one: it needs two nested enumerations, a
   clock and a universal guest. Small Π₁ machines like Goldbach do not need these.
   So ~200 is a research target, not an engineering one.

Smaller, still-valid improvements inside the current design: cheaper DEC
(carry-shift variants with shared continuations, or slack cells), and superoptimization
of repeated fragments (brief §7.3), with the beep state excluded.
