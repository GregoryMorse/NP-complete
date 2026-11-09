# 03 — Z_FACTOR (`native/zfac.py`, 324 states): `Quasihalts zfacMachine ↔ SentenceF`

Prerequisites: plan 01. Plan 02 is recommended first, as the template.

This plan also builds the **FACTOR glue**, which plans 04 (DLOG) and 05 (GI) reuse:
- the new-instance copy;
- the result path;
- the decider-fuel dispatch;
- for DLOG, also the unary conversion.

Build it as separate files with machine-generic statements.

**What changes vs zp2.** There is no certificate counter and no verifier run. After
the instance is copied, a native routine computes the truth bit `o`, and the decider
phase is zp2's. 106 zfac-specific transitions. Measured overlaps:
- 37 of them are identical in zdl **and** zgi (the glue): states
  `NI TL GC GP GCM TS FR0 FR1 FE ER20 ER21 DP30 DP31 W1 CX SINC JINC SOV JOV2`;
- 68 are identical in zdl (glue + Horner conversion `TS2 HPF HPD CA0 CA1 SW RW DR DE DU`).

## 1. Trusted definitions (`ZP/DefsF.lean`, mirrors `ref/zfac_ref.py`)

```lean
/-- `ref/zfac_ref.numbers`: `1b` appends binary digit `b`, `0` starts the next number,
a trailing lone `1` is ignored. -/
def numsAux : List Bool → Nat → List Nat
  | [], cur => [cur]
  | [true], cur => [cur]
  | true :: b :: r, cur => numsAux r (2 * cur + if b then 1 else 0)
  | false :: r, cur => cur :: numsAux r 0
def numbers (s : List Bool) : List Nat := numsAux s 0
def inLF (s : List Bool) : Bool :=
  match numbers s with
  | k :: a :: _ => (List.range (k + 1)).any fun d => decide (2 ≤ d) && a % d == 0
  | _ => false
def CorrectF' (J S : Nat) : Prop := CorrectF inLF J S      -- plan 01 step H
def SentenceF : Prop := SentenceC (CorrectF inLF)
```

Sanity checks (`ZP/ChecksF.lean`, by `decide`):
- `numbers` on ~10 strings, compared with `python3 -c 'from zfac_ref import numbers; …'`;
- `inLF` on the first 30 shortlex strings;
- the first beeps of `zfac_ref.zp_beeps()`;
- `zfacMachine.table.length = 324`.

## 2. Generated files and numbering

Run:
- `gen_table.py zfactor_native zfacMachine`, giving `ZP/TableF.lean`;
- `gen_logic.py zfac`, giving `ZP/LogicF.lean` (`zfacLogic`, `zfacCert`, `QF.*`).

**Numbering rule, extended.** zfac's own new states get fixed numbers (129, 130, …)
that zdl and zgi **inherit** for the same names. So `gen_logic.py` takes a parent chain:
`zp2 ← zfac ← {zdl, zgi}`. Then also generate:
- `zfGlue` = `zpBase` + the 37 shared glue transitions (in `ZP/LogicF.lean`);
- `zfConv` = `zfGlue` + the 31 conversion transitions shared with zdl.

Prove:
```lean
theorem zfGlue_ext_zfConv : zfGlue.Ext zfConv
theorem zfConv_ext_zfac   : zfConv.Ext zfacLogic
```
both by `ext_of_extB (by decide +kernel)`. State the glue lemmas for `zfGlue` and the
conversion lemmas for `zfConv`.

## 3. Pair boundary

From `native/zp2.py`/`zfac.py`: the start `I0 → JOV2` and every successor
(`SINC`/`JINC`/`SOV`/`JOV2`) now go to **`NI`**, not `GRB`. So:

```lean
def layF (J S : Nat) : ZC := hdR QF.NI (1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S))) []
```

(Check the exact head position on the Python machine.) The successor lemmas are
copies of `sincL`/`jincL` (`ZP/Pair.lean:1032`) that end in `NI`. Put them in
`ZP/GlueF.lean`, stated for `zfGlue`.

## 4. Phases (Python trace first: run `zfac.py` on `s = '1011'` and print the tape at each phase boundary)

1. **New instance** (`NI → TL → DG2 → GC … GP → TS`). It writes `M_2` and `H`, walks to
   `M_g` and copies `s` left of `H` with zp2's `GC` loop. Reuse `gcLoop` (zpBase). The
   end of the source meets the empty slot after `M_2`, and `GP` on `B` goes to `TS`.
   Lemma `niPhase : zfGlue.Reach (layF J S) (convStart s)`.

2. **Conversion (Horner, unary)** (`TS TS2 HPF HPD CA0 CA1 SW RW DR DE DU`).
   - The streaming parser state is (finished numbers, current value, pending lone `1`).
   - Machine invariant: the targets left of the separator are unary blocks
     `… n_3 M n_2 M n_1 M`, the current one being `1^cur`.
   - One-digit lemma: from `HPF` with the next copy cell(s) `1 b`, the current block
     `1^t` becomes `1^(2t+b)`. Inside, the "mark all, append marked, unmark" sweep is
     three loops over the block. Each is an `rep`-indexed induction like `copyLoop`.
   - Separator lemma: a `0` opens a new block (`SW`).
   - End lemma: the copy is used up (`HPF` on `M`, or `HPD` on `M` for a trailing lone
     `1`), giving `RS1`.
   - Conclude by induction on `s`, with `numsAux` as the spec:
     `conv : zfConv.Reach (convStart s) (divStart (numbers s))`.
   - This is the piece DLOG reuses, so make the statement independent of what
     `RS1` does.

3. **Divisibility** (`RS1 RS2 RS3 SA SK SK2 RST BACK CHK KC ND SHR`), with
   `K = n_1 = k` on the right and `A = n_2 = a` on the left.
   - `RS1`/`RS2` restore K to 1s and check `|K| ≥ 2`. Otherwise `FR0`; also `FR0` when
     there is no second number (`RS3` on `B`).
   - Inner loop, one test of `d = |K|`, `d ≥ 2`:
     - invariant: `i` cells of A marked (left to right), `i % d` cells of K marked;
     - K resets when full (`SK2` on `M`, then `RST`);
     - A used up (`SA` on `B`/`M`) goes to `CHK` (restore A) and then `KC`;
     - K untouched (`i % d = 0`) means `d ∣ a`, giving `FR1`; otherwise `ND → SHR`
       turns K's last cell into `M` (so `d := d-1`) and returns to `RS1`.
     - Lemma `divTest d a : (d ∣ a → reaches FR1-config) ∧ (¬ d ∣ a → reaches RS1-config with d-1)`,
       by induction on `a`, with the `i % d` bookkeeping as `Nat.mod` facts.
   - Outer loop: induction on `d` from `k` down to 2 gives
     `o = decide (∃ d, 2 ≤ d ∧ d ≤ k ∧ d ∣ a)`. Bridge it to `inLF` with a small lemma
     about `List.any` over `List.range`.
   - Edge case `a = 0`: A is used up at once, so `FR1` (every `d` divides 0), which
     matches the ref.

4. **Result** (`FR0/FR1 → FE → ER1 → ER2o → DP3o → (W1) → FB`). `FR o` writes `o` in
   the gap, `FE` erases the left side, and zp2's `ER1`/`ER2o` read it. In zfac,
   `ER2o` on `B` skips the gap. `DP3o` on `B` writes the truth flag `M [1]`, and `FB`
   writes `M_3`.
   - Show the resulting tape is exactly zp2's `TR j Sb o` from `ZP/Pair.lean:806`
     (state `GRB`).
   - Lemma `resultPhase` (for `zfGlue`).

5. **Decider.** `CX` on `B` now always goes to `DW1` ("every BLK is decider fuel"). So
   `decFuel` must be re-proved for `zfGlue` with this dispatch. `blkDecStep`/`blkDecLast`
   use `CX`/`BD*`, which are volatile, so they must be regenerated. Then `runFrom`,
   `dOk*`, `dBad*` and `beepStep` are reused through `Ext`. Check each on symexec
   before assuming reuse.

6. **`pairF_main`**: compose 1–5 and the successors, exactly like `pair_main`. Then
   `lmacroSim_of_pairs zfacLogic (CorrectF inLF) layF k0 …`, where `k0` is the step
   count `I0 → JOV2 → NI` (expected 2). Finally:
   ```lean
   theorem zfac_quasihalts_iff_sentence : Quasihalts zfacMachine ↔ SentenceF
   theorem zfac_quasihalts_iff_InP : Quasihalts zfacMachine ↔ InP (fun s => inLF s = true)
   ```
   Add the first theorem to `Challenge.lean`/`Solution.lean`/`comparator.json`.

## 5. Not in scope

"`InP L_F` ↔ factoring is in P" (binary search on `k`) is a function-problem statement.
Leave it on paper (docs/native.md) unless the user asks.

## Files

`DefsF`, `ChecksF`, `TableF`, `LogicF` (generated), `CompileF` (cert + `Ext`),
`GlueF` (phases 1, 4, 5 and the successors; reused by 04/05), `ConvF` (phase 2;
reused by 04), `DivF` (phase 3), `PairF` (`pairF_main`, top theorems).

## Estimate

~2500–3500 lines. The conversion is the hardest part, because of nested sweeps with
marks.

## Status: DONE

Files: `ZP/DefsF`, `ChecksF`, `TableF`, `LogicF`, `CompileF`, `PairF`, `MainF`.
`PairF.lean` (~1400 lines) is the reusable material for plans 04 (DLOG) and 05 (GI):

- Copied from `Pair.lean` and *refitted* (`/tmp/refit.py`-style script: re-derive each segment's fuel `k`
  with `symexec.py` against the new logic file): `gcEnd` (now `GC → GP → GCM`, needs the decider
  flag cell to start `Rest`), `setup/runFrom/dPhase` (extra hypothesis `∃ R', Rest = 1 :: R'`),
  `sinc*/jinc*` (end in `QF.NI`).
- Conversion to unary: `dig2/dig3/dstep/dEnd/sepStep/endM/endLone` (generated), `dloop` (doubling),
  `digitStep`, `convLoop` (spec: `lyt`, `lay1`, `parseState`, `numbers_eq`).
- Divisibility: `aIter1/aIter2/endDiv{M,B}/endNdiv{M,B}/rsStart/fr0*` (generated), `aLoop`, `rsG`,
  `roundDiv/roundNdiv`, `divLoop`, `truthPhase` (conv + division, spec `inLF`).
- Result: `frPath0/1` (+ `hdR_zeros`: blank prefix), `newInstF`, `pair_mainF`.
- DLOG/GI reuse: `ni0/ni2`, `layF`, `newInstF`'s shape, `convLoop` (DLOG only), `frPath*`,
  `dPhase`, `pair_mainF`'s proof text (replace the truth phase).
