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

### Factoring in P (`native/zfac.py`, 324 states)

Same interpreter, clock, enumeration and decider phase as Z_P v2. The verifier
phase (certificate counter and verifier runs) is replaced by a native brute-force
truth routine.

- **Instance.** `s` is parsed left to right into numbers: a pair `1b` appends the
  binary digit `b` to the current number, a `0` starts the next one. `k` is the first
  number and `a` the second. `s ∈ L_F` iff some `d` with `2 ≤ d ≤ k` divides `a`
  (fewer than two numbers: `s ∉ L_F`). `(a, min(k, a−1))` asks whether `a` has a
  nontrivial factor up to `k`; binary search on `k` factors, so `L_F ∈ P` iff
  factoring is in P.
- **Copy.** A new instance writes `M_2` and `H` and walks to `M_g`. The
  interpreter's own copy loop (`GC`) then copies `s` to the left of `H`. At the end
  of the source, an empty slot after `M_2` routes to the truth routine instead of
  the `Q` setup.
- **Unary conversion (Horner).** The copy is consumed from its right end, which is
  `s[0]`, and `H` becomes the first blank of a gap. Targets grow leftwards beyond a
  separator `M`. For a digit, the added bit is appended already marked; every
  unmarked `1` is then marked and a marked cell appended; finally all cells are
  unmarked. That gives `T := 2T + b` in 11 states.
- **Divisibility.** For `d = |K|` down to 2, the routine tests `d | |A|`. It marks
  one cell of `A`, then one of `K`, and resets `K` as soon as it is full. `A` is used
  up exactly when `K` is all 1s. A failed test turns `K`'s last cell into `M`.
- **Result.** The result `o` is written into the first gap cell and the left side is
  erased. The interpreter's own post-run dispatch (`ER1`/`ER2o`) then reads `o`. It
  writes the truth flag `M [1]` after `M_2`, then `M_3` and the decider fuel.

### Discrete log mod primes in P (`native/zdl.py`, 400 states)

Built on the FACTOR machine: same glue, conversion and result path. The last four
numbers are `(k, h, g, p)`; with three numbers, `k = 0`. `s ∈ L_D` iff `p` is prime
and `g^e mod p = h` for some `0 ≤ e ≤ k`.

- **Primality.** `D` is a copy of `P` at the left edge. For `d = p−1` down to 2,
  `D` shrinks at its left edge and `d | p` is tested by marking one cell of `P`,
  then one of `D`, with an eager reset. When `D` is down to one cell, `p` is prime,
  and that cell is `y = 1`: the layout is `Y M P M G M H M K`.
- **Loop.** `Y` is compared with `H` by marking both. If they are equal, `s ∈ L_D`.
  Otherwise one cell of `K` is marked (none left: `s ∉ L_D`) and `Y := Y·G mod P` is
  computed. For every cell of `G` and every cell of `Y`, the next cell of `P` is
  marked, and `P` resets when full. `Y` is then rebuilt at the left edge from
  `P`'s marked cells.

### Graph isomorphism in P (`native/zgi.py`, 415 states)

Built on the FACTOR glue and result path. The instance is unary: the run lengths of
`s`, read last to first, are `m`, then the edge list `X` up to the first empty run,
then the flattened `m`-column adjacency matrix `H` up to the next one (an entry is an
edge iff it is ≥ 2). `s ∈ L_GI` iff some injective `w: {1..t} → {1..m}` maps the edges
of `X` one-to-one onto the edges of `H` (see `ref/zgi_ref.py` for why this is
equivalent to GI). There is no conversion: the reversed copy of `s` only has its 0s
turned into separators.

- **Search.** `w` is a stack at the left edge, each entry followed by its own `M`.
  Push a copy of `m`. While the top equals another entry (cells of both marked in
  turn), decrement it. An emptied top is popped, and popping checks the stack below
  it, so every injective `w` (the empty one too) is checked exactly once.
- **Check.** For an edge `(x, y)`, `a = w_x` is found by marking one cell of `x` per
  skipped entry of `w`. The row part then skips `m·(a−1)` entries of `H`: once per
  cell of `m`, one entry per cell of `a` but its last. An entry is skipped by marking
  its first cell. The column part skips `b − 1` more. Whether a row part is under way
  is read off `m`'s marks. The entry reached must be an undeleted edge, and is
  deleted by marking its second cell (the scan that unmarks the skipped entries finds
  it). Finally every edge of `H` must be deleted. A failure unmarks everything and
  decrements the top.

### Linear-time multiplication (`native/zmul.py`, 408 states)

The guest is Z_P v2 plus a queue of `|J|` stacks; the clock is
`T = (|s|+2)·2^|J| − 1`, one fuel block `M 1^(|s|+1)` and `|J|` short blocks `M 1`.
Entries with `t = 0` change meaning:

- `w 1 0` is a **switch**. The head cell is erased. The cells `h+1, h+2, …` up to the
  first blank are appended to the back of the queue as a stack. The stack at the front
  is taken out and written *reversed* from cell `h` on. Then the step rotates past the
  entry and one more (`k = 0`).
- `1 0 0` is a proper **halt**, with output `out` = cells `0 … h−1`. `0 0 0` and the
  time-out are failures.

`J` is correct on `s` iff the run halts properly within `T` and, with `U = out 0 s`
parsed by the FACTOR rule (pairs `1b` are binary digits, `0` starts the next number),
`N[0] = N[1]·N[2]` (missing numbers are 0). So a correct `J` writes `x·y` in front of
the head, where `x, y` are the first two numbers of `s`. Every run is a decider run, and
the outcome 0 beeps. The machine therefore quasihalts iff some `J` is correct on every
`s`. That holds iff multitape Turing machines multiply in linear time:

- A `k`-tape machine is simulated with `O(1)` guest steps per step, with `T`'s constant
  set by padding `J`. Each stack carries tags at both ends, so after a switch the head
  shows which stack came in and which end is up. A stack is reversed each time it comes
  in, so within two passes of the queue (`O(|J|)` switches) the wanted stack comes in
  the wanted way up. A spare cell at the head absorbs the erasure.
- Conversely, the model is a tape plus a constant number of stacks, each used at both
  ends (deques). A deque costs amortized `O(1)` on two stacks.

Layout: `M_g J M_1 s M_2 fuel B storage`. The storage holds the queue front first,
each stack as `M c_1 c_2 …`. The walker appends one empty stack per step back
through `J`.

- **Switch.** The head cell becomes a marker `M`. The cells left of it are taken from
  the far end (next to the gap) one at a time and inserted at the front of the storage
  by a shift chain. When the marker comes up it is erased and a terminator `M` is
  inserted. The storage front then shows `M`, so the back stack is popped from its end
  into the blank cells left of `H`, which reverses it.
- **Check.** `1 0 0` keeps `H` as `M`. After the left side is erased, `ER1` finds it,
  makes it the separator `0`, blanks `M_2` (the copy loop then ends at a blank) and
  copies `s` reversed to its left. The FACTOR conversion turns `out 0 s`, read from
  `M_g` leftwards, into unary numbers `… y M x M z`. Then `z = x·y` is checked by
  marking: each cell of `y` marks all of `x`, and each cell of `x` marks one cell of
  `z`. `M_2` is restored on the way to the dispatch.

### Linear-size NTT circuits (`native/zntt.py`, 564 states)

The machine checks a *chain circuit* version of NTT-LIN (`ref/zntt_ref.py`): there is
a `c` such that for every `n`, with `p` the least prime `≡ 1 (mod n)` and `N = c·n`,
some chain circuit of `N` records over `F_p` computes `DFT_n`. Record `j` holds a
pointer `u_j` (or none), a coefficient `b_j` and a root `z_j`, and computes

    node_j = [j < n] x_j + node_{j-1} + b_j · node_{u_j}.

The last `n` records are the outputs. Output `k` must have row `(z_k^t)_{t<n}` with
`z_k^n = 1`, and the power sums `Σ_k z_k^t` must vanish for `1 ≤ t < n`. Since
`p > n`, Newton's identities then force `{z_k}` to be exactly the `n`-th roots of unity,
so the rows of `DFT_n` appear in some order. A fan-in-2 gate `a x + b y` takes three
records (zero, `+ a x`, `+ b y`), so the two statements differ only in the constant.

- **Rulers.** `P` grows by `n` until a divisor test finds it prime. `D = 2, 3, …`
  marks once per cell of `P` and resets when full. A reset writes a marker, so
  "full at the end, no marker" means `d = p`. `W = c·n + 1` is built from the C and
  Nn rulers.
- **Records.** For each cell of `C` (a round), one record per cell of `Nn` is
  appended: header `F G O P`, four copies of `P` (acc, E, z, b) and one of `W` (u).
  Each new round clears `O` in the records already built.
- **Evaluation.** One pass per input `t` uses push evaluation in column order. A
  pointer is decremented once at the start of the pass and once per earlier column.
  It is *captured* (exactly two unmarked 1s) in its own column. Then each unit of
  `acc_j` adds 1 to record `j+1` and `b_r` to every capturing record.
- **Outputs.** At an output, `acc = E` is checked destructively. Then
  `E := z·acc`, and the register `S` (the marked cells of `P`) gets `z·acc` as well.
  After pass `t < n−1`, `S` must be 0. After the last pass, every `E` must be 1.
- **Search.** An odometer runs over `(z, b, u)` of all records. A success moves to
  `n + 1`. Exhaustion beeps and moves to `c + 1`, `n = 1`.

The first refutation is `c = 1` at `n = 2`. `c = 2` passes `n = 2` and then searches
`n = 3`, which does not finish in simulation. So the tests check the first beep and
evaluate hand-built `DFT_2`/`DFT_3` circuits and their perturbations against the
reference.

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

- **Lean.** The Lean statement in `formal/` is about v2 (278 states); the macro
  simulation `ZP.zp_macroSim` is still open.
- **Paper proof.** The NP-hardness of the v2 language L has only the padding sketch
  above.
