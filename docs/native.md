# Z_P v2: the natively designed machine

`machines/zp_native.txt` (388 states) is built from `native/zp2.py`. That file is a
135-state machine over four logical symbols, `B M 0 1`. `native/compile2.py` turns it into
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

The design invariant is that the logical machine never meets an undefined transition.
The tests exercise this, but it is not proved.

### Not yet done

- **Lean.** The Lean formalization in `formal/` covers v1, not v2.
- **Paper proof.** The NP-hardness of the v2 language L has only the padding sketch
  above.
