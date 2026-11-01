# Z_P v2: the natively designed machine

`machines/zp_native.txt` (278 states) is built from `native/zp2.py`. That file is a
129-state machine over four logical symbols, `B M 0 1`. `native/compile2.py` turns it into
a 2-symbol machine. The reference semantics live in `ref/zp2_ref.py`; this note explains
them and the tape layout.

## Guest model

A code `P` is any bit string. The interpreter works on the cyclic string
`R = reverse(P) + '0'`, which it rotates once before the first step. An *entry* at the front of `R` is parsed
cyclically as `w d 1^k 0`. One guest step works like this:

1. Read the head cell `a` (blank, 0 or 1).
2. Rotate `R` by ι(a) entries, where ι(blank, 0, 1) = 0, 1, 2.
3. Spend one unit of the step budget. If none is left, the run ends with NAC.
4. Peek at `w = R[0]`, `d = R[1]` and `t = R[2]`.
5. If `t = 0`, halt: the result is ACC if `w = 1`, otherwise NAC.
6. Otherwise:
   - write `w`;
   - move right if `d = 1`, else left (the head stays put at cell 0);
   - rotate past the entry, then past `k + 1` more entries.

The instance `s = ''` and the candidate `J = ''` are examined like any other.

The guest tape is one-way infinite, and the guest never writes a blank. A three-symbol
Turing machine state becomes three consecutive entries. A jump is a cyclic entry
distance, so codes can be padded with unused entries without changing what they do.

## Definitions

- `L = { s : some c in {0,1}^(|s|+1) has run(s, c, |s|+1) = ACC }`.
  - L is in NP, and it is NP-hard by the usual padding argument.
- Candidate `J` is correct on `s` iff `(run(J, s, T) = ACC) == (s in L)`, where
  `T = (|s|+2)^(|J|+2) − 1`.
- Z_P v2 enumerates `J` in shortlex order. For each `J` it enumerates `s` in shortlex
  order and beeps at the first `s` where `J` is wrong.
- Therefore it quasihalts iff some `J` is correct on every `s`, iff L ∈ P, iff P = NP.
  - A time-out counts as rejection. That is harmless: a candidate that accepts exactly
    L within `T` steps already gives a polynomial-time decider.

## Tape layout

Logical cells are stored as pairs of cells: `B=00`, `M=01`, `0=10`, `1=11`.

Between runs the tape reads:

    M_g J M_1 s M_2 C M_3 M B_R … M B_1

| part | contents |
|---|---|
| `C` | the certificate counter, `|s|+1` bits, counting down. In a decider run it is replaced by a truth flag: `M` or `M 1`. |
| `B_j` | fuel blocks of `|s|+1` cells. They form an odometer in base `|s|+2`. The double `M` before the first block marks the end of the fuel. |

The number of blocks R depends on the run:

- a verifier run uses 1 block;
- a decider run uses `|J|+1` blocks, built by a walker `M` that moves through `J`.

During a run, the left side holds three things, from left to right:

1. **The queue `Q`.** This is the rotated code. A rotation moves the bits of one entry
   from Q's right end to its left end, so Q drifts left.
2. **A blank gap.** Jump tokens `M` sit here. A "recording" rotation leaves a token in
   place of `w`, `d` and every `1`. Each token is then consumed by one further rotation.
3. **The guest tape, reversed.** It reads `c_max … c_h H c_(h−1) … c_0`, with the head
   marker `H` just right of the scanned cell `c_h`.

## Verification

- `tests/test_native.py` (in CI) runs two checks against `zp2_ref.zp_beeps`:
  - the logical machine, 12 beeps;
  - the compiled 2-symbol table, simulated with `native/psim.c`, 40 beeps.

  Both checks compare the decoded `(J, s)` at every beep.
- 120 beeps have been checked for the compiled table.

### Merging don't-care states

`native/dcmin.py` merges states that have *undefined* transitions. A merge is accepted
only if the merged machine agrees with the original on every defined transition. So on
any run of the original that never meets an undefined transition, the merged machine
behaves identically.

The greedy merge is followed by an exact one. `native/exact.py` encodes the
minimum compatible-state partition as SAT (pysat, CaDiCaL), seeded with the greedy result
as a phase hint, with bound one below it. `native/runexact.py` stores the class map; `build.py`
replays a stored map from `native/exact_<name>.json` and checks it transition by
transition. P = NP drops from 285 (greedy) to 278, P = PP from 301 to 295, P = PSPACE from 296 to 291.

The design invariant is that the logical machine never meets an undefined transition.
The tests exercise this, but it is not proved.

### P = PP (`native/zpp.py`, 295 states)

The P = PP machine has the same guest model, clock and enumeration. Its language is

    L_PP = { s : at least half of the c in {0,1}^(|s|+1) have run(s, c, |s|+1) = ACC }.

This is a self-padded majority language; the "at least half" threshold is
PP-complete just as "more than half" is. Reference: `ref/zpp_ref.py`.

The machine adds an accept counter `A = 1^(|s|+1)` after `C`:
`… C M_3 A M_4 fuel`. Every accepting certificate decrements `A`. The leading bit
of `A` turns 0 exactly at the 2^|s|-th accept, so the threshold check needs no
comparison. If `C` underflows first, the truth is 0.

### P = PSPACE (`native/zps.py`, 291 states)

The language is a quantifier game over the certificate bits:

    G(s) = Q_0 c_0 … Q_n c_n : run(s, c, n+1) = ACC

- `Q_n` is ∃ and the quantifiers alternate going left.
- This is QBF with a linear-time matrix; it is PSPACE-complete by padding. Dummy
  certificate bits fix the quantifier pattern, and unread bits do not change the
  value.
- Reference: `ref/zps_ref.py`.

`C` walks the game tree depth-first, taking `c_i = 1` as each node's first child, with
short-circuiting. That is why no value stack is needed. After a run with result r,
the machine walks left from C's last bit:

| bit | meaning | action |
|---|---|---|
| `0` | the node's second child is done | set the bit to 1 and go up |
| `1`, r dominant (1 for ∃, 0 for ∀) | short-circuit | go up |
| `1`, r not dominant | — | write 0 and run the second child |
| reaching `M_2` | root reached | the root's value is r |

This walk replaces the NP machine's decrement; the walk states differ only in r and
the parity.

### NP = coNP (`native/zconp.py`, 317 states)

Same interpreter and clock. Nondeterminism enters at fresh cells. When the head
moves right onto a never-visited cell, it consumes a choice: 1 writes `1`, 0 leaves
the cell blank. The start cell is not a choice.

- `run_nd(P, x, T)` accepts iff some choice sequence makes `core(P)` accept `x`
  within `T` steps. `core(P)` is `P` with trailing 1s removed.
- `L = { s : run_nd(s, '', |s|+1) }`. L is NP-complete and monotone: s ∈ L implies
  s1 ∈ L.
- `J` is correct on `s` iff `run_nd(J, s, T)` ⟺ s ∉ L. The machine beeps at the
  first wrong `s`.
- A prover can only extend the instance with 1s. Monotonicity makes the
  verifier "read up to the first blank, then check a certificate" sound. So a
  correct `J` exists iff NP = coNP.

The choice string `D` sits after the fuel, behind one blank, with a pointer `M`.
A fresh cell fetches the bit after the pointer. At the end of `D` the choice
defaults to 1 and `D` grows. A rejecting run backtracks `D` depth first: strip
trailing 0s, turn the last 1 into 0, and shift the pointer back to the front. The
fuel is then erased and rebuilt; it has the same length, so `D` stays put. An
emptied `D` ends the phase with result 0.

The slot between `M_2` and `M_3` is empty in the verifier phase. In the decider
phase it holds the truth bit.

Beyond 13 beeps the reference itself needs exponentially many runs. The tests
therefore add instance checks that exercise multi-run searches.

### Compiler

`native/compile2.py` stores each logical cell as a pair of cells. Each logical state
enters its pair from a fixed side, chosen per state. Three things keep the 2-symbol
machine small:

- **Pair skip.** A state acts on the first cell read alone when the second cell cannot
  change the outcome.
- **Known symbol.** If only one logical symbol with the first-read cell value can occur,
  the second cell is never read.
- **Known cells.** Helper states that walk over (or rewrite) a cell whose value is
  already known define only that one symbol. The other symbol is a don't-care, which
  the merger exploits.
- **Write skip.** If both symbols with the first-read cell value have the same
  transition, the state writes the pair without reading the second cell.

Encoding design invariants as don't-cares also helps. For example:

- after the ι countdown, `c_h` is blank;
- `|R| = 1` implies `R = '0'`, and `|R| = 2` implies `d = 0`;
- no tokens exist before a recording rotation;
- a verifier run has one fuel block.

Each such invariant is commented in `zp2.py`.

### Not yet done

- **Lean.** The Lean formalization in `formal/` covers v1, not v2.
- **Paper proof.** The NP-hardness of the v2 language L has only the padding sketch
  above.
