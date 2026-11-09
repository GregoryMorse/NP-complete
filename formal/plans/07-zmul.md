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

### Status update (retargeted interpreter lemmas)

- `ZP/MulRot.lean`, `ZP/MulFuel.lean`, `ZP/MulInterp.lean`: copies of `Rot`, `Fuel`, `Interp` with `zpBase` -> `zmBase`, in namespace `ZP.Mul`. They build; only the two halting peek segments (`segHalt`, `segShort2`) fail on `zmBase` (the peek of `t = 0` entries is what zmul changes) and are removed from the copy.
- Findings from `zmul` traces (entry `FBACK` on `w d 0`): `w=0,d=0` reaches `ER20`/`DP10` (outcome 0), `w=1,d=0` reaches the new states `mK1/mK2` (output check), `d=1` reaches the switch states (`mRX`, `mPB0`, `mPB`, `mL1`, ...). These three exits are the new segments to prove before `MulRun` (copy of `Run.lean`, whose step uses `segHalt/segShort2`).
- Next: new halt/switch peek segments, `MulRun` with the queue relation `StorRel`, mixed-width fuel, check.

### Status update (halting peek segments)

- `ZP/MulInterp.lean` now has the halting peeks: `segHalt0`, `segShort1`, `segShort2_0` (outcome 0, `w=d=t=0`; these only use transitions shared with `zp2`, so they are stated for `zmBase` and reach `hdR Q.DP10 [1] W`), and `segHalt1`, `segShort2_1` (outcome 1, `w=1,d=0,t=0`).
- **Important:** every segment that passes through a transition zmul changes (the `t = 0` peeks `PKT01/PKT11`, the switch, the output check) cannot be proved for `zmBase`; it must be stated for `zmulLogic` and combined with the `zmBase` lemmas through `zmBase_ext_zmulLogic.reach`. So `MulRun` should work with `zmulLogic.Reach`, lifting the `zmBase` pieces (`Rot`, `Fuel`, normal-step segments, `segHalt0`).
- Exit shape of the outcome-1 halt: `hd FBACK (Qw ++ [2,2,3] ++ 0^g ++ 0 :: (Lw ++ [0])) (1 :: (Rw ++ 1 :: W)) ⟶ hdR mK1 [2] (Rw ++ 1 :: W)`. `Rw` (the guest cells left of the head) is the output, `Lw`/`Qw`/the gap are blanked, and `mK1` starts the multiplication check on `0 Rw M W`.
- A Python mirror for designing the remaining segments is `formal/scripts/symexec.py` run with `LOGIC=LogicMul LOGICID=zmul`.
- Still to do: the switch peek and `switchStep` (shift chain, terminator, pop) with `StorRel`, `MulRun`, mixed-width fuel and its build, the `mK*` output check (`mulCheck`), `pair_mainMul`, `MainMul`, Challenge/Solution entries.

### Status update (mixed-width fuel; switch analysis)

- `ZP/MulFuel.lean`: the odometer is now over `List Dg` (`Dg = Nat × Nat`, block width and digit): `FWr`, `valr`, `Dig`, `full`, `rad`, `fuel` (decrement, same width list) and `valr_full : valr (full ds) + 1 = rad ds`. For the zmul fuel take `ds = (0,·) × |J|` followed by `(|s|,·)` (wide block most significant), giving `(|s|+2)·2^|J| - 1`. `borrow`/`fuel` accept a tail that is empty, `M`-led, or blank-led (the blank is the `B` before the storage).
- **Switch, observed with the concrete simulator** (`peek w 1 0`, start `hd FBACK (Qw ++ [2,3,r0] ++ 0^g ++ 0 :: (Lw ++ [0])) (1 :: Rw ++ 1 :: W ++ 1 :: F)` with `F = FWr ds ++ 0 :: ST`; `ST` = storage text):
  - storage text is `⋃ over the queue, back first` of `1 :: bitsOf st` (`st` in cell order `h+1, h+2, …`, i.e. `bitsOf Lt`, which is `Lw` reversed);
  - phase 1 (`mGS`, `mGW`, `mTB`, `mTK`): mark the cell before the head `M` with a marker `M'`; then loop: `mTK` on the leftmost remaining `Lw` cell `a` blanks it, `mC_a` sweeps right to the separator `B`, `mQ*` inserts `a` at the front of `ST` (shift of the whole storage by one, non-identity: needs a list induction), `mRT/mRX/mRT2/mTB` return; iteration `T(a :: Lw', ST') → T(Lw', a :: ST')` (the gap grows by one blank);
  - phase 2: marker reached (`mCM`): it is erased and `M` inserted at the storage front;
  - phase 3 (pop): `mPB0` sweeps to the end of `ST`, `mPB` takes the last bit (blanking it), `mL_b`/`mLL_b` carry it left to the last blank cell before the head's `M`, `mBK` returns; at the stack's `M` it is erased (`mE1`) and `RGQ1` returns to `RTW`;
  - end state `hd RTW (Qw ++ [2,3,r0]) (0^y ++ 0 :: (Lw2 ++ ch2 :: 1 :: …))` with `Lw2 ++ [ch2] = bitsOf front` (`ch2 = 0`, `Lw2 = []` if the front stack is empty), so `post` (rotation) applies to the code `r0 :: true :: false :: rest` as in the normal step.
- **Capacity condition (open, no counterexample found).** The pop deposits the front stack into the blank run left of the head `M`; if the stack has more bits than that run (`g + |Lt_now| + 3`, where the gap `g` between code and `Lw` depends only on the code, e.g. 7 for `J = 10`, 11 for `1010`, 18 for `1011`, not on `|s|`), `mLL` would sweep over the code and the layout would be destroyed. A hand-built overflow (simulator) does destroy it, so the interpreter theorem needs an invariant "front stack size <= g + |Lt| + 3" along reachable runs. Evidence so far (Python runs of `LogicMul` from a hand-built run-start layout `hdR GC (M M P M) (s M M 1^(|s|+1) (M 1)^|J| B M^|J|)`): the machine outcome equals `ref/zmul_ref.py` on all 7938 pairs `|J| <= 6`, `|s| <= 5`, including 2034 with non-empty pops and stacks up to 19 cells, and no deposit overflowed; random longer `J` (up to 30 bits) with stacks of 16-32 cells agree as well. Random programs reaching stacks of 80-100 cells within 300 guest steps exist (e.g. `J = 1000110111101110110001111`, `s = 0`) but the machine run did not reach their pops within 40M simulated steps, so they are untested. The invariant is neither proved nor refuted. A proof needs to bound stack sizes (tape cells reachable within `clockMul` steps) by `g`, which depends only on the code, and that looks false for adversarial programs; if it is, `Quasihalts zmulMachine <-> SentenceMul` does not follow from `runMul` alone.
- Remaining (not started): the loops above as Lean lemmas (`ins` induction, outer `Lw` loop, pop loop, `switchStep` with `StorRel` and the capacity invariant), `MulRun`/`runMul` theorem over `zmulLogic.Reach`, the `mK*` check (`mulCheck`), `pair_mainMul`, `MainMul`, Challenge/Solution entries.

### Capacity condition: RESOLVED (it is an invariant, not a machine bug)

The previous note measured `g` only near the start of a run and concluded that it "depends only on the code".
It does not: the code `Q` drifts left by every rotation, so the gap grows at every guest step, and the cells a
switch removes from the guest tape stay in the room in front of `H` as blanks. Measure the **room**

    rho := g + |Lw|          (layout  code ++ 0^g ++ 0 :: (Lw ++ [c])  at FBACK / BK2; Lw = bitsOf Lt.reverse)

i.e. the number of cells strictly between the code's right end and `H`, up to the constant 2. Then:

1. **rho never decreases from one guest step to the next.** In Lean terms, with the copied lemmas of `MulInterp`/`MulRun`:
   - `cdStep` already proves `g' = H.length + g + 1`, so every count-down rotation gives `g ≤ g'`;
   - `tokens` already proves `g' = a + y + 2`, so `post` gives `y + 2 ≤ g'` (state it as `y + 1 ≤ g'`);
   - a move left (`segMv0e`, `segMv0c`) passes `y = g` and `Lw2 = Lw ++ [r0]` or `Lw`, so rho grows;
   - a move right onto a used cell (`segMv1`, `Lw = Lw2 ++ [ch2]`) has `y = g`, `|Lw2| = |Lw| - 1`:
     `rho' = g' + |Lw| - 1 >= g + 1 + |Lw| - 1 = rho`;
   - a move right onto a fresh cell (`Lw = []`): the new head cell comes out of the gap, `y + 1 = g`,
     `rho' = g' >= y + 1 = g = rho`;
   - a switch keeps the region between code and `H` cell for cell (it only rewrites it), then `post` adds `>= 1`.
   So the only change to the copied zp2 lemmas is to **replace `∃ g', 1 ≤ g'` by the quantitative bound**
   (`g ≤ g'` for `cdStep`/`countdown`, `y + 1 ≤ g'` for `tokens`/`post`, and in `peek` the bound that
   makes `rho' ≥ rho`, i.e. `g + 1 ≤ g'` when the move consumed a cell of `Lw` or of the gap, `g ≤ g'` otherwise;
   the `1 ≤ g'` facts still follow). These are copies in namespace `ZP.Mul`, so `Run.lean`/`Interp.lean` are untouched.
2. **Every stack in the queue has length ≤ rho** (`Cap Q rho : ∀ st ∈ Q, st.length ≤ rho`):
   - at the run start the queue is `|J|` empty stacks;
   - normal steps do not change the queue and do not decrease rho;
   - a switch pushes `Lt` (`|Lt| = |Lw| ≤ rho`) and pops the front `F` (`|F| ≤ rho` by the invariant), then rho does not
     decrease, so `Cap` holds again.
3. **The pop fits.** Before the pop the region between the code and `H` is `g + |Lt| + 2` cells, all blank
   (the shift chain moved `Lt` into the storage and erased the head cell). The deposit needs `|F|` cells and a
   blank separating it from the code, so `|F| ≤ g + |Lt| = rho` is enough. Take this as the hypothesis of
   `switchStep` and compute the new gap exactly: `y = g + |Lt| + 1 - |F|` (cells are conserved), so
   `y ≥ 1` and the output layout is the `RTW` layout that `post` takes.

So `MulRun` carries `StorRel Q storage ∧ Cap Q (g + |Lw|)` (plus zp2's `1 ≤ g`) through the induction on the run,
and `switchStep` takes `F.length ≤ g + Lt.length` as a hypothesis. No change to `native/zmul.py` or the table is needed.

**Evidence** (`formal/scripts/zmulcap/run.py SEED N MAXLEN_J MAXLEN_S`: a C simulator of the logical machine,
started from the run-start layout and compared with `ref/zmul_ref.correct`). There were 12,800 random pairs with
506,586 non-empty pops in total, in runs with `|J| ≤ 3, |s| ≤ 60`; `|J| ≤ 4, |s| ≤ 40`; `|J| ≤ 6, |s| ≤ 24`;
`|J| ≤ 8, |s| ≤ 16`; `|J| ≤ 2, |s| ≤ 20`. Results: no outcome mismatch and no overflow, and every deposited cell
had at least 20 blanks between it and the code. Over 6,800 of these pairs (99,460 pops), rho was also measured
at every guest step and never decreased. The earlier test stopped at `|s| ≤ 5`, so it never exercised this.
Runs with long `J` and `s` that hit the 4·10^9-step cap print `ABNORMAL ... STEPS`; that is the step cap, not an error.

Next (unchanged order): the shift-chain, terminator and pop loops as Lean lemmas, `switchStep` with the hypothesis
above, `MulRun` (the `runMul` theorem over `zmulLogic.Reach`, carrying `StorRel` and `Cap`), the `mK*` check
(`mulCheck`), `pair_mainMul`, `MainMul`, Challenge/Solution entries.
