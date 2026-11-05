# 07 — Z_MUL (`native/zmul.py`, 403 states): `Quasihalts zmulMachine ↔ SentenceMul`

Prerequisites: plan 01; plan 03 helps (the output check reuses the FACTOR number
format, though `zmul.py` reimplements it on top of zp2, not zfac).

This machine has a **new guest model**. The interpreter's halting path changes, and
there is a new *switch* entry that moves whole stacks between the tape and a queue.
So a large part of N3 (`Run.lean`, parts of `Interp.lean`) must be re-proved for the
new step. Expect it to be the largest job after NTT.

## 1. Trusted definitions (`ZP/DefsMul.lean`, mirrors `ref/zmul_ref.py`)

Mirror `zmul_ref.run(P, x, T, r)` literally, including:

- **state:** cyclic code `R` (zp2's `rot`, `rotN`, `entryOnes`), a finite guest tape
  (use `List (Option Bool)` or zp2's `Nat → Option Bool` with an explicit used
  length), head `h`, and a queue `List (List Bool)` that starts as `r = |J|` empty
  stacks;
- **each step:** rotate by `iota(tape h)`; if `T = 0`, fail; peek `w, d, t`. The ref
  pads `d` and `t` with `'0'` when `|R|` is 1 or 2; zp2's `R.getD i false` does that
  already. Then:
  - `t = 0 ∧ d = 0`: halt. `w = 1` returns `some (cells 0..h-1)`, `w = 0` returns
    `none`.
  - `t = 0 ∧ d = 1` (switch):
    - pop cells `h+1, h+2, …` up to the first blank into a stack (in order);
    - erase cell `h`;
    - append the stack to the queue;
    - pop the queue front and write it **reversed** from cell `h` on;
    - set `k = 0`.
  - `t = 1`: as zp2.
  - Then `R, k := rot R`, followed by `k + 1` more rotations. For a switch, the entry
    has `t = 0`, so `rot` itself returns `k = 0`; the ref's explicit `k = 0` is
    overwritten but agrees. Mirror the ref's code path (`rot`, then `k + 1` more
    rotations) and pin it with a sanity check.
- `clockMul J s := (s.length + 2) * 2 ^ J.length - 1`;
- `checkMul out s := let N := numbers (out ++ false :: s) ++ [0,0,0]; N[0] = N[1] * N[2]`
  (`numbers` from `DefsF`, plan 03; if plan 03 is not done, move `numbers` into a
  shared trusted file `ZP/DefsNum.lean`);
- `CorrectMul J S := match runMul (str J) (str S) (clockMul …) (str J).length with
  | some out => checkMul out (str S) = true | none => False`, with a `Decidable`
  instance;
- `SentenceMul : Prop := SentenceC CorrectMul`.

Sanity checks: run `zmul_ref` on hand-made programs that switch, and pin
`runMul` on them by `decide`. Also pin the first beeps.

## 2. Generated files

Run:
- `gen_table.py zmul_native zmulMachine`;
- `gen_logic.py zmul`, with parent zp2.

Zmul changes 16 **more** zp2 transitions than the other machines:
`BEEP,M`, `DP30,M`, `DP31,M`, `DP40/41` (1, M), `DW40/41,M`, `EAs,B`, `FB,B`, `GHH1,M`,
`PKT01,0`, `PKT11,0`, `WB30/31,M`. So define `zmBase` = `zpBase` minus those, and retarget
whatever zp2 lemmas survive to `zmBase`, as in plan 01 step F. Note that **BEEP
itself changes**, so `beepStep` is per-machine.

## 3. Layout

`M_g J M_1 s M_2 fuel B storage`:
- the fuel is one block `M 1^(|s|+1)` and `|J|` short blocks `M 1`;
- the storage holds the queue front first, each stack as `M c_1 c_2 …`;
- the walker appends one empty stack per step back through `J`.

## 4. Work items

1. **Fuel with mixed widths.** `ZP/Fuel.lean`'s odometer has every block the same width
   `n+1`. Generalize `fuel`/`valr` to a list of widths
   (`valr` = mixed-radix value), or prove a second instance for widths
   `[n+1, 1, 1, …]`. The value must be `(n+2)·2^|J| − 1`. Prove it the way
   `valr_full` (`ZP/Pair.lean:996`) does.
2. **Fuel build.** The walker through `J` builds `|J|` short blocks plus the storage
   (one empty stack per position). Adapt `decFuel`/`wbLoop`.
3. **Interpreter.** The normal step (`t = 1`) and the rotations are unchanged
   (`Rot`, `Interp.segA/segB/...`, via `Ext zmBase`). New pieces:
   - **halt** `1 0 0`: keeps `H` as `M`, and the output is the cells left of the head.
     `0 0 0` and time-out fail.
   - **switch** `w 1 0` has three parts:
     - shift chain: the head cell becomes a marker `M`; cells to its left (the cells
       `h+1…`, because the guest tape is stored reversed) are taken from the far end
       one at a time and inserted at the storage front;
     - terminator: when the marker comes up, it is erased and a terminator `M`
       inserted;
     - pop: the back stack is popped from its end into the blank cells left of `H`,
       which reverses it.

     Each is a loop lemma over a `List Bool`. Prove the composite
     `switchStep : Reach (pre-switch config z, queue Q) (post-switch config per runMul)`.
   - Then redo `runI`/`runFrom` (`ZP/Run.lean`, `ZP/Pair.lean:597`) for `runMul`. The
     induction is the same; the extra state is the queue ↔ storage relation
     `StorRel Q storage`.
4. **Check** (after a proper halt):
   - `ER1` finds `H`, makes it the separator `0`, blanks `M_2` and copies `s` reversed
     to its left.
   - The FACTOR-style conversion (here inside `zmul.py`) turns `out 0 s` into unary
     `… y M x M z`.
   - Then `z = x·y` is checked by marking (each cell of `y` marks all of `x`, each cell
     of `x` marks one cell of `z`). Lemma `mulCheck x y z : reaches accept ↔ z = x*y`,
     a double induction like plan 04's modular multiply but without the mod.
   - `M_2` is restored on the way to the dispatch.
5. **Compare and successors.** The outcome 0 beeps (`J+1`, `s` reset), the outcome 1
   gives `s+1`. Same `absStepC` as zp2, so `lmacroSim_of_pairs` applies.

## 5. Top

```lean
theorem zmul_quasihalts_iff_sentence : Quasihalts zmulMachine ↔ SentenceMul
```

"⇔ multitape TMs multiply in linear time" stays on paper.

## Estimate

~5000–7000 lines. Plan at least 4 sessions:
1. Defs, Checks, generation, base.
2. Fuel and the switch loops.
3. The `runMul` interpreter theorem.
4. The check and the top theorem.

## Status (in progress)

`ZP/DefsMul.lean` (trusted definitions, §1) is done and builds: `runMulAux/runMul`, `clockMul`, `checkMul`,
`correctMulB`, `CorrectMul`, `SentenceMul`. The guest tape is a `List Bool` (its support is an initial segment).
Sanity checks reproduce the first refutations of `ref/zmul_ref.py` (`('', '')`, `('0', '')`, `('1','11011')`, `('00','')`),
including that `J = '1'` is correct on all instances before `'11011'`.
Everything from §2 on (generated files, fuel, switch loops, interpreter theorem, check) is still to do.

### Status update (generated files and certificate)

- `gen_table.py zmul_native` and `gen_logic.py zmul` (parent: zp2 directly) generate `ZP/TableMul.lean` and `ZP/LogicMul.lean` (169 logical states, 190 slots); the CI loops include them.
- `ZP/CompileMul.lean`: `zmulCert_ok` and `zmulMacroSimC` build with no sorry.
- Next: `zmBase` (zp2 minus the 16 extra transitions), the Ext facts, mixed-width fuel, switch loops.

### Status update (zmBase)

- `gen_logic.py basemul` generates `ZP/LogicBaseMul.lean` (`zmBase`: zp2 minus the 75 transitions changed by the derived machines and zmul, with zmul's beep state 36); CI regenerates it.
- `ZP/ExtChecks.lean`: `zmBase_ext_zmulLogic` (kernel-checked).
- Note: `zmBase` has a different beep state than `zpBase`, so the zpBase-based lemmas (Fuel, Rot, Interp, Run) must be re-proved or re-derived for `zmBase`; that, the mixed-width fuel, switch loops, the `runMul` theorem and the check are still to do.
