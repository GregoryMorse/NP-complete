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
  `T = (|s|+2)^(|J|+1) − 1`.
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

`J` is correct on `s` iff the run halts properly within `T`, `out` is a pair numeral
`1 b_1 1 b_2 … 1 b_k` (`k ≥ 0`), and, with `U = out 0 s` parsed by the FACTOR rule (pairs
`1b` are binary digits, `0` starts the next number), `N[0] = N[1]·N[2]` (missing numbers
are 0). Since a pair numeral contributes exactly one number, this says `out` is `x·y`
written in pairs, where `x, y` are the first two numbers of `s`. The machine checks the
pair form while it scans `out` from its last cell: a `0` where a token `1` belongs, or odd
length, takes the outcome-0 path. (Without that check, an `out` with a stray `0` shifted
the parse; `out = 0` gave `N = [0, 0, x, …]` and passed for every `s`. The 403-state table
of 2026-11-11 had that defect.) Every run is a decider run, and
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

### Linear-size NTT circuits (`native/zntt.py`, 469 states)

The machine checks a *chain circuit* version of NTT-LIN (`ref/zntt_ref.py`): there is
a `c` such that for every `n`, with `p` the least prime `≡ 1 (mod n)` and `N = c·n`,
some chain circuit of `N` records over `F_p` computes `DFT_n` up to a diagonal.
Record `j` holds a pointer `u_j < j` (or none) and a coefficient `b_j`, and computes

    node_j = [j < n] x_j + node_{j-1} + b_j · node_{u_j}.

The last `n` records are the outputs, and output `k` uses its own coefficient as its
root `z_k = b_k`. Output `k` must have row `(z_k^t)_{t<n}`. The power sums
`s_t = Σ_k z_k^t` must vanish for `0 < t < n`, and `s_n` must not. Since `p > n`,
Newton's identities make the `z_k` the `n` distinct roots of `x^n = c` for some
`c ≠ 0`. So the outputs compute `DFT_n · diag(ζ^t)` with `ζ^n = c`, rows in some order.
A fan-in-2 gate `a x + b y` takes three records (zero, `+ a x`, `+ b y`), an output
takes two more gates, and the diagonal costs `n` gates. So the two statements
differ only in the constant.

- **Rulers.** `P` grows by `n` until it is prime. The test copies `P` to `D` and
  tests `d = p−1, …, 2` by marking `D` once per cell of `P`, resetting it when full.
  `p` is used up exactly when `D` is full. The pointer ruler `W` starts at two cells
  and grows by one per record built, so the pointer field of record `j` has `j + 2`
  cells.
- **Records.** For each cell of `C` (a round), one record per cell of `Nn` is
  appended: header `F O P`, three copies of `P` (acc, E, b) and one of `W` (u).
  Each new round clears `O` in the records already built.
- **Evaluation.** One pass per input `t`. The pass starts by resetting every `acc`
  to `[record = t]`, then evaluates by pushing values forward in column order. A
  pointer is decremented once per earlier column and is *captured* (exactly two
  unmarked 1s) in its own column. When the cursor enters an output, `acc = E` is
  checked destructively. Each unit of `acc_j` then adds 1 to record `j+1` and `b_r` to
  every capturing record `r`; at an output it also adds `z` to `E` and to the register
  `S` (the marked cells of `P`).
- **Power sums.** After pass `t < n−1`, `S` must be 0. After the last pass `S` must
  be nonzero, which is one look at the first cell of `P`.
- **Search.** An odometer runs over `(b, u)` of all records. A success moves to
  `n + 1`. Exhaustion beeps and moves to `c + 1`, keeping `n`. This is sound because
  for `c ≥ 2` a circuit for `(c, n)` gives one for `(c+1, n)`: insert `n`
  pass-through records after the inputs. The two paths share the code that erases
  the records. The last cell of `Nn` tells them apart: after a success every cell
  of `Nn` is marked by the passes, while the odometer clears the marks.

The first refutations are `c = 1` and `c = 2`, both at `n = 2`. `c = 3` passes `n = 2`
and then searches `n = 3`, which does not finish in simulation. So the tests check two
beeps. They also run hand-built `DFT_2`/`DFT_3` circuits (including roots of `x³ = 6`
mod 7 and outputs out of order) and perturbations of them against the reference.
The previous design (564 states before tuning) also had a bug: after a success the
pass marks on `Nn` were not cleared, so `p` came out wrong for `n ≥ 2`.

### Promise-P = promise-BPP (`native/zbpp.py`, 333 states)

Same guest model, clock and enumeration as Z_P v2. For `s` with `n = |s|` and
`N = 2^(n+1)` certificates, let `acc` count the `c` with `run(s, c, n+1) = ACC` and
`rej = N − acc`. The promise problem `CAPP` has

- YES instances: `4·acc ≥ 3N`;
- NO instances: `4·rej ≥ 3N`;
- every other `s` is outside the promise.

This is circuit acceptance probability with gap 3/4 vs 1/4, in the self-padded form of
`L_PP`; it is complete for promise-BPP under the padding reduction (amplify to error
1/4 first; unread certificate bits do not change the ratio). `J` is correct on `s` iff
`s` is outside the promise or `run(J, s, T)` agrees with it. So the machine quasihalts
iff some `J` decides `CAPP` on its promise within the clock, iff **promise-P =
promise-BPP**. This is the promise version on purpose: promise-P = promise-BPP implies
P = BPP, but P = BPP (for languages) is not known to imply it, and BPP has no known
complete language. Reference:
`ref/zbpp_ref.py`.

The machine adds an accept counter `A` and a reject counter `R` after `C`:
`… C M_3 A M_4 R M_5 fuel`. Both start at `⌈3N/4⌉ − 1`, i.e. `1^(n+1)` with the
second cell turned 0 (`1` for `n = 0`). An accepting certificate decrements `A`, a
rejecting one `R`, then `C` is decremented as in zp2. A borrow out of `A`'s leading bit
(the `⌈3N/4⌉`-th accept) gives truth 1, one out of `R` truth 0. If `C` underflows
first, `s` is outside the promise: everything right of `M_2` is erased and the machine
moves to `s + 1` without running `J`.

### NP ⊆ P/poly (`native/zppoly.py`, 325 states)

Same guest model and the same NP-complete language `L` as Z_P v2. A *degree* `K` (any
bit string; only `|K|` matters) fixes the budget `T(K, n) = (n+2)^(|K|+1) − 1`. For
each input length `n` the machine searches for an *advice program* `a`: a guest code
that decides `L` on every `s ∈ {0,1}^n`. A run of `a` is charged `|a|` steps up front,
`prun(a, s, T) = run(a, s, T − |a|)` if `|a| ≤ T`, else a time-out. `K` is good on `n`
iff some `a` with `|a| ≤ T(K, n)` is right on all of `{0,1}^n`.

The machine enumerates `K` in shortlex order. For each `K` it runs through
`n = 0, 1, 2, …`, for each `n` through `a = '', '0', '1', '00', …` and for each `a`
through `s ∈ {0,1}^n` in binary order. A wrong `s` moves to the next `a`; a correct last
`s` moves to `n + 1` with `a = ''`. It beeps when `|a|` reaches `T(K, n) + 1`, and
moves to the next `K` with `n = 0`. So it quasihalts iff some `K` is good on every `n`,
iff `L` has polynomial-size programs that run in polynomial time, iff `L ∈ P/poly`,
iff **NP ⊆ P/poly** (`L` is NP-complete under polynomial-time reductions, which
preserve P/poly). Reference: `ref/zppoly_ref.py`.

Layout: `M_g K M_1 a M_a s M_2 C M_3 …`. `K` plays `J`'s part (the walker builds
`|K|+1` fuel blocks) and is stored last bit first, so `K + 1` runs from the left; the
decider's code is `a`, the field before its source `s`, and `s` is a binary counter of
fixed length `n`. After a block is built, the cell after `M_2` tells the phase (`1`:
verifier fuel, `M`: decider fuel), instead of zp2's count of fields.

- **Charge.** Before a decider run, zp2's guest copy loop copies `a` to the left of
  `M_g` as tokens. The fuel is then decremented once per token through zp2's own
  odometer loop: each return of the loop moves a marker one token on. Exhausting the
  fuel there means `|a| > T(K, n)`: the machine beeps (`BEEPX`), increments `K`, erases
  everything right of `M_1` and goes on with `n = 0`, `a = ''`.
- **Next instance.** Correct: `s + 1` in binary; an overflow appends a cell to `s`
  (`n + 1`) and deletes `a` cell by cell. Wrong: `s := 0^n`, `a := a + 1` (shortlex,
  with the same increment as `s`; a carry out of `a` lengthens it, shifting `M_a` by one
  cell). zp2's beep state now only marks a wrong answer.

Only the first refutation (`K = ''`, `n = 1`) is in reach of the tests; the second
needs every advice program up to length `T('0', 4) = 35`. The tests also follow the
first six events (`n` passed with advice `a`, or a beep) through `zppoly_ref.events`.

### L = P and L = NL (`native/zlp.py`, 373 states; `native/zlnl.py`, 415 states)

The decider of both machines is a **multihead read-only** guest (`ref/zmh_ref.py`):
code, cyclic `R`, entries and the step loop as in Z_P v2, but the input `x` is read only
and there are `|P| + 1` heads, all at position 0 at the start. Positions are
`0 … n+1`; `0` and `n+1` are end markers and read as blank. The current head starts
as head 0. With `t = 1`:

- `w = 1` moves the current head right (`d = 1`) or left (`d = 0`), staying at the ends;
- `w = 0` makes the next (`d = 1`) or previous (`d = 0`) head current, staying at the
  last and the first.

A log-space machine is a multihead two-way DFA (Hartmanis 1972) that runs in
polynomial time; one step of a `k`-head automaton costs `O(k)` steps here, and the
clock `(|s|+2)^(|J|+1) − 1` covers it once `J` is padded. Conversely `run_mh(J, x, T)`
takes space `O(|J| log |x|)`. So the deciders are exactly the log-space machines.

- **L = P.** The truth is `L_P = { s : run_mh(s, s, |s|+1) = ACC }`: program `s`, run
  on its own text with `|s|+1` heads. `L_P` is in P and P-complete under log-space
  reductions: the heads serve as the cells of a polynomial-time machine's tape (a head
  at position 0 is a 0, at position 1 a 1; the current head is the tape head), the
  first `|x|` steps of the program write the input `x`, and padding makes `|s| + 1` at
  least the running time. So the machine quasihalts iff `L_P ∈ L` iff **L = P**.
- **L = NL.** The truth is `L_NL = { s : some c ∈ {0,1}^(|s|+1) has run1(s, c, |s|+1)
  = ACC }`, where `run1` is Z_P v2's run with a **one-way** head (`d = 0` leaves the
  head in place). `L_NL ∈ NL`: guess `c` cell by cell as the head reaches it, keeping
  the rotation state, the head position, the current cell and a step counter. It is
  NL-hard: the configuration graph of a log-space NTM on `x` has polynomially many
  nodes, and a program of polynomial size hard-wires it (one block of entries per
  configuration, the certificate bit under the head choosing the successor, then a
  move right); padding covers the steps and certificate cells used. So the machine
  quasihalts iff `L_NL ∈ L` iff **L = NL**. Reference: `ref/znl_ref.py`.

Both machines share `native/zmh.py`. During a multihead run the tape is

    Q gap c H M_g J M_1 s M_2 … fuel B storage

The countdown cell `c` holds the symbol under the current head (blank at the end
markers); zp2's ι countdown runs on it. The storage holds one unit per head,
`M x_1 … x_n 0` (`x = s`), with a marker cell after the scanned cell: `B` for the
current head, `M` for the others. The unit's `M` is position 0, its last `0` position
`n+1`. Head 0 is the last (rightmost) unit, head `i+1` the unit left of head `i`. The
act (entered right of `H`) skips to the end of the fuel and then to the current
marker, the first blank of the storage. A move swaps the marker with its neighbour
unless the scanned cell is the unit's `M` (left) or position `n+1` (right); a head
switch turns the current marker into `M` and the neighbouring unit's marker into `B`
(staying at the first / last unit). The new scanned symbol is then carried into `c`,
and the entry is recorded as in zp2. A halt is zp2's; the storage is erased later
with the rest of the far right (the erase loop after the comparison).

- **Units.** `M M s 0` is appended at the far right by a copy loop over `s` (the old
  current marker becomes `M` on the way, the new unit's marker becomes current). The
  decider gets one unit when the walker reaches `M_1` and one per step of the walk back
  through `J` (`|J| + 1`); after each unit the head returns straight to the walker.
- **zlp.** The walk back ends at home without writing `H`; then the head looks at the
  field after `M_2`. A bit is `C = 1^(|s|+1)`, the verifier's flag and head counter:
  one unit per cell, consumed to 0s, then the verifier run (program `s` on input `s`,
  `|s| + 1` heads, `T = |s| + 1`). There is one verifier run; its outcome is the
  truth. `M` is the decider's truth flag: decider run of `J`. The setup writes `H`,
  then zp2's placeholder for `c` and code copy, with code `J` or `s`.
- **zlnl.** The verifier runs are zp2's (certificate counter `C`, guest tape copied from
  `C`, the guest tape left of `H`) with one change: `write w, move left` becomes
  `write w, stay`. `VG1` puts a dummy `0` between `H` and `M_g`, so during a verifier
  run the cell right of `H` is a bit and during a decider run it is `M_g`; the act
  looks there once and dispatches. The decider setup skips `s`, marks `M_2` and joins
  zp2's code copy; the verifier setup joins zp2's guest copy.

The tests compare beeps with the references, run instances whose programs switch
heads, and check the act on every storage with `|x| ≤ 3` and up to 3 heads.

### Linear-time GF(2) matrix product (`native/zmm.py`, 494 states)

Z_MUL with a different output check (`ref/zmm_ref.py`): the guest model, the clock
`T = (|s|+2)·2^|J| − 1`, the outer loop and the beep on the first wrong `s` are
Z_MUL's. The instance is `s = 1^m 0 w`: `B` is the `m × m` matrix `w[0 : m²]`
(row-major, padded with 0s) and `A` is the rest of `w` cut into rows of length `m`
(the last row padded), so `A` has `r = ⌈(|w| − m²)/m⌉` rows. `J` is correct on `s` iff
the run halts properly within `T` and `out`, padded with 0s, starts with the `r × m`
product `C = A·B` over GF(2).

The machine quasihalts iff some multitape Turing machine computes the GF(2) product of
two `m × m` matrices in time `O(m²)`, linear in the input. This is a **proxy**, not
ω = 2 (see below). The guest model and multitape machines simulate each other in
linear time (Z_MUL). The encoding converts to and from the plain one (`1^m 0 A B`) in
linear time. An `r × m` by `m × m` product is `⌈r/m⌉` square products when `r ≥ m`, and
one square product with `A` padded when `r < m`; either way the input has at least
`max(m², r·m)` cells. If `|w| ≤ m²`, `C` is empty.

The check works on the copy of `s` that Z_MUL makes next to `out` (`H` stays `M` and
is the separator `Ms`). The ruler `1^m` is reused as the accumulator, so the check
needs no space beyond `s`:

    M_g out Ms [acc, hole H] Mr [B, hole P] M [A] s-end

- Setup: the `0` after `1^m` becomes the hole `H`, `w` moves one cell (its first cell
  becomes `Mr`), and a reverse shift leaves `P`, the only blank of `B`, in front of `B`.
  `Mr` holds `a`, the `A` entry of the current row of `B` (`M` = 0, blank = 1).
- A step moves the cell `v` after `P` into `P` (so `P` slides through `B`), XORs
  `a·v` into the accumulator cell after `H`, and moves `H` one cell on. When `H`
  reaches `Mr` a row of `B` is done: `Mr` is reset, `H` is rewound, and the next `a`
  is fetched (the front of `A`, which becomes `M`; 0 past the end of `A`). When `P`
  reaches the `B`/`A` boundary a row of `C` is done.
- The first row is a dry run with `a = 0`. It finds the end of `B` by counting: each
  row of `B` marks one ruler `1` as `0`, and when none is left the boundary `M` is
  inserted at `P` (the reverse shift moves all of `w`). If `P` reaches the end of `w`
  first, `|w| ≤ m²` and the check passes.
- At every row end the accumulator must be `0^m` (a 1 left: the check fails); then the
  next `m` cells of `out` (consumed from the `M_g` side; missing cells read as 0) are
  loaded into it. So the products of a row XOR the accumulator back to 0 iff the row
  of `out` is right. If `A` is used up the check passes; otherwise `B` is shifted back.
- Outcome `o`: the blanks between `M_g` and `Ms` become 0, `Ms` becomes `o`, the four
  blank-terminated stretches further left are erased, and zp2's `ER1` takes over.

The tests run guest programs that write a fixed string (`C`, `C` with one bit
flipped, or random) on random instances with `m ≤ 3`, and compare beeps.

### Not attempted

- **promise-BQP = promise-P** (or BPP = BQP): the truth would need exact or
  approximate amplitudes of a quantum circuit. The natural complete problem
  (estimate one amplitude of a circuit to 1/poly) needs arithmetic on numbers whose
  size grows with the circuit, and approximations with error control. Too big for a
  native routine.
- **Deterministic polynomial identity testing** (the derandomization of PIT): the
  truth is "this arithmetic circuit computes the zero polynomial", which needs
  polynomial arithmetic (or Schwartz–Zippel with exact big-integer evaluation over
  all points of a grid). Possible in principle, but much larger than the machines here.
- **ω = 2**: the statement "for every ε > 0 there is an `O(n^(2+ε))` algorithm" is Π₃
  (∀ε ∃ algorithm ∀ inputs), not Σ₂, so it is not a quasihalting statement of this
  kind. Z_MATMUL above is the Σ₂ statement "exactly linear time on multitape
  machines, over GF(2)". Neither statement is known to imply the other.

### Compiler

`native/compile2.py` stores each logical cell as a pair of cells. Each logical state
enters its pair from a fixed side, chosen per state (the start state from the left,
as `formal/ZP/Compile.lean` assumes). Three things keep the 2-symbol
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

- **Lean.** The Lean statement in `formal/` is about v2 (278 states). The step from
  the 129-state logical machine to the table is proved (`formal/ZP/Compile.lean`);
  the macro simulation of the abstract program by the logical machine,
  `ZP.zpLogic_macroSim`, is proved too (per-pair lemma `ZP.pair_step`, `formal/ZP/Pair.lean`).
- **Paper proof.** The NP-hardness of the v2 language L has only the padding sketch
  above.
