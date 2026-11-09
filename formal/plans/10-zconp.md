# 10 — Z_coNP (`native/zconp.py`, 317 states): `Quasihalts zconpMachine ↔ SentenceConp`

**Status: done.** `ZP.zconpQuasihalts_iff_sentence` (`ZP/MainConp.lean`) is in `Challenge.lean`, `Solution.lean`, `comparator.json`; axioms: propext, Classical.choice, Quot.sound.

Prerequisites: plan 01 (generic pipeline), the zp2 development (`Run`, `Pair`, `Logical`), and the lessons of
plan 07 (a machine that changes zp2 transitions which `zpBase` keeps needs its own base, and segments through
changed transitions are stated for the machine itself and combined with base lemmas via `Ext.reach`). Plan 06's
`nodePS` is the template for the search induction.

Reference: `ref/zconp_ref.py`; design: `docs/native.md` § "NP = coNP"; machine: `native/zconp.py`.

## 0. Already done (this commit)

- `ZP/TableConp.lean` (`gen_table.py zconp_native`, 317 states), `ZP/LogicConp.lean` (`gen_logic.py zconp`,
  138 logical states, 151 slots), `ZP/LogicBaseConp.lean` (`gen_logic.py baseconp`: `zcBase` = zp2 minus the 69
  transitions changed by the derived machines **and** zconp; same beep state as zp2).
- `ZP/CompileConp.lean`: `zconpCert_ok`, `zconpMacroSimC` (the table simulates `zconpLogic`).
- `ZP/ExtChecksConp.lean`: `zcBase_ext_zconpLogic`.
- CI regenerates all four files. Everything builds; no `sorry`.

`zpBase` is **not** contained in `zconpLogic`: zconp changes 10 of its transitions
(`PUTH,B` `QN2,M` `BEEP,M` `DP30,M` `DP31,M` `DP40,1/M` `DP41,1/M` `EAs,B`). So, as with `zmBase` in plan 07,
copy the zp2 lemmas that survive (`Rot`, `Fuel`, `Interp` minus the right-move and halting segments, the copy
loops `gcLoop`/`qcLoop` minus the `QN2` exit) to `zcBase` in namespace `ZP.Conp`, and state everything that
passes through a changed transition for `zconpLogic`.

## 1. Trusted definitions (`ZP/DefsConp.lean`, mirrors `ref/zconp_ref.py`)

```lean
/-- `core P`: P with its trailing 1s removed (`P.rstrip('1')`). -/
def core (P : List Bool) : List Bool
/-- One run with the choice string D (choices past the end of D are 1).
    Mirrors `run_choice` literally: zp2's step plus, on a right move onto a cell beyond `top`,
    consume the next choice; choice 1 writes 1, choice 0 leaves the cell blank. -/
def runChoice (P x : List Bool) (T : Nat) (D : List Bool) : Bool × Nat   -- result, choices used
def runND (P x : List Bool) (T : Nat) : Prop := ∃ D : List Bool, (runChoice (core P) x T D).1 = true
instance : Decidable (runND P x T)    -- only D of length ≤ T matter (each choice costs a step)
def inLC (s : List Bool) : Prop := runND s [] (s.length + 1)
def CorrectConp (J S : Nat) : Prop := runND (str J) (str S) (clock (str J) (str S)) ↔ ¬ inLC (str S)
def SentenceConp : Prop := SentenceC CorrectConp
```

Write `runChoice` as a copy of `runAux` (`ZP/Defs.lean`) with `top`, the choice index and `D` threaded
through. The ref clamps `top` at `max(|x| - 1, 0)`, and the start cell is never a choice. Keep the trusted
search **existential**. The ref searches depth first; the equality of the two is a theorem (§4e), not a
definition. Checks in `ZP/ChecksConp.lean` (`decide`): `core`, `runChoice` on hand-picked programs that use
choices, `inLC` on the first ~15 strings, and the first 3 beeps of `zconp_ref.zp_beeps()`. They are
exponential, so keep them tiny. The ref warns that beyond 13 beeps it needs exponentially many runs.

## 2. Layout

Between runs: `M_g J M_1 s M_2 [t] M_3 M B_R … M B_1 B D`.
- **Verifier phase**: code `s`, input empty, one fuel block (`T = |s| + 1`), the slot `[t]` empty.
- **Decider phase**: code `J`, input `s`, `|J| + 1` blocks (zp2's clock), the slot holds the truth bit `t`.
- `D` sits after the fuel, behind one blank, as `d_1 … d_j M d_(j+1) … d_k` (pointer `M` after the consumed choices).

Print the tape at `GRB`, `GC`, `QS`, `PF`, `FT3`, `DP3*`, `BT`, `RS2`, `ER3`, `EX3`, `BEEP` for
`J = ''`, `s = '0'` and a decider pair that uses choices (`python3 native/zconp.py`, `native/logic.py`'s
`run`/`show`) before writing any statement.

## 3. Interpreter with choices (`ZP/ConpInterp.lean`, `ZP/ConpRun.lean`)

1. **Q setup with `core`**: `QN2,M → QS`. `QS` skips trailing 1s, then the zp2 copy loop `QC` runs on the rest.
   Lemma: the setup leaves `rot (reverse (core P) ++ [0])`, i.e. zp2's `setup` with `core P` for `P`.
2. **Right move** (`GH w1` → `PUTH` → `PF`): `PF` reads the cell beyond the new head:
   - a bit: not fresh, go on as zp2 (`RGQ1`). This is zp2's `segMv1` restated for `zconpLogic`;
   - blank: **fresh**, fetch a choice (`FT1 FT2 FT3 FTW0/FTW1 RTC1`): sweep right over the fuel to `D`, pass the
     consumed prefix to the pointer, take the next bit (or start/extend `D` with a 1 at its end), move the
     pointer one cell right, return; choice 1 writes 1 into the fresh cell (`RTC1`), 0 leaves it blank.
     Lemma `fetch`, with the `D` layout as a parameter.
3. **Fresh ⇔ blank.** The ref's test is `h > top`; the machine's is "the cell is blank". They agree because the
   guest writes its head cell on every step (`w`), so inside `[0, top]` only the head cell can be blank. Carry
   this as part of the run invariant (`z.WF`-style: every cell of `Lt` is a bit).
4. **The run theorem** `runFromC`: from the run-start layout with `D` (pointer at the front) the machine reaches
   the result dispatch with `runChoice (core P) x T D` as the result and with `D` replaced by
   `D ++ 1^e` (the lazily added 1s) and the pointer after the used choices. A copy of zp2's `runFrom`/`runI`
   induction, with `(D, k, top)` in the state.
5. **D is always used up.** The backtrack below strips from `D`'s right end and stops at the first 1, so it is
   right only if no unused bits are left after the pointer, i.e. the run used every choice of `D`. Lemma: if the
   run with `U` used `|U|` choices, the run with `next U = A ++ [false]` (where `U = A ++ true :: 0^j`) agrees with
   it until the `|A|+1`-th choice, hence also reaches it (same time, same tape). So it uses at least `|A| + 1`
   choices. Induction over the run, comparing two runs with a common choice prefix.

## 4. Search, phases, dispatch (`ZP/ConpSearch.lean`, `ZP/PairConp.lean`)

a. **Accept** `DP31`: verifier phase (slot `M`): write `t = 1` (`EAs`, which also erases fuel and `D`), decider fuel.
   Decider phase: slot `1` (s ∈ L): **BEEP**; slot `0` (s ∉ L): correct, `EAs`.
b. **Reject** `DP30 → BTR1 BTR2 → BT`: from `D`'s end erase the `M` and trailing `0`s, turn the last `1` into the
   pointer cell, write `0` after it (`RS0`), shift the pointer back to the front (`RS2 RS0 RS1` loop), then erase
   and rebuild the fuel (`ER3 ER4 → GRB`, same length, so `D` stays put). Lemma `backtrack`: `D = U` (used up)
   becomes `next U` with the pointer at the front; or, if `U` has no `1`, `BT` reaches the blank: **exhausted**.
c. **Exhausted** `EX1 EX2 EX3`: erase the fuel; verifier phase: `t = 0` (`EX4`), decider fuel; decider phase:
   slot `0`: **BEEP**; slot `1`: correct, `EAs`.
d. **Outer loop** (`EBs`, `SINC`, `JINC`, `W1`, `FB`, `GRB`/`BD*`): `BD1 BD2 BD3` and the outer-loop states are
   changed, so redo zp2's `phase1`/`blkCopy` dispatch lemmas for `zconpLogic`; the `BN*`/`COPY`/`CR*`/`CL*` loops are unchanged
   (`zcBase`).
e. **Depth-first search = existential** (pure math, no machine). Let `next U` = `U` with trailing `false`s
   removed and its last `true` made `false` (`none` if there is none). Let `pad U` = `U ++ 1^(T+1-|U|)` read as a
   binary number, most significant bit first. Facts:
   - `runChoice` depends only on the first `used` choices (`used` = its second component);
   - `pad (next U) < pad U`: the search terminates; use `pad` as the well-founded measure;
   - **no accepting `D` is skipped**: every `D` with `pad (next U) < pad D ≤ pad U` extends `U`'s used prefix
     (`D = A ++ true :: 0^j ++ _`), so it gives the same run, and that run rejects.
   So, by induction on `pad`: started from `D = []` (`pad = 2^(T+1) − 1`), the search accepts iff `runND`.
   This is plan 06's `nodePS` with ∃ only. Prove it on `runChoice` alone, then combine it with `runFromC` and
   `backtrack` into the machine lemma `searchC`: from the phase start with empty `D` the machine reaches
   accept (`DP31`) iff `runND`, else exhausted (`EX1`).
f. **Pair lemma** `pair_mainConp J S`: new instance → verifier phase (`searchC` with `s`, `[]`, `|s|+1`) → `t`
   → decider fuel → decider phase (`searchC` with `J`, `s`, clock) → beep iff `¬ CorrectConp J S` → successor
   (`absStepC CorrectConp`). Then `lmacroSim_of_pairs zconpLogic CorrectConp …`, `zconpMacroSimC`,
   `quasihalts_iff_of_macroSimC`.

## 5. Top (`ZP/MainConp.lean`)

```lean
theorem zconp_quasihalts_iff_sentence : Quasihalts zconpMachine ↔ SentenceConp
```

Add it to `Challenge.lean`, `Solution.lean`, `comparator.json` (`ZP.DefsConp`, `ZP.TableConp` in the challenge
imports).

"`SentenceConp` ↔ NP = coNP" stays on paper (`docs/native.md`: `L` is NP-complete and monotone, so a correct `J`
is an NP verifier for co-L, and conversely). Formalizing it needs `ZP/Complexity.lean`'s `InNP` and the
hardness argument of `Hard.lean` for the nondeterministic guest; write a design note before any Lean.

## Estimate

~4000–6000 lines, 3–4 sessions:
1. `DefsConp`, `ChecksConp`, the `zcBase` copies (Rot/Fuel/Interp/copy loops), the `core` setup.
2. `fetch`, the right-move segments, `runFromC` with the fresh ⇔ blank invariant, "D is used up".
3. The DFS lemma (§4e), `backtrack`, exhaustion, `searchC`.
4. Dispatch, outer loop, `pair_mainConp`, top theorem, Challenge/Solution.

## Checklist

- [x] generated files, certificate, `zcBase` (§0)
- [ ] `DefsConp` + `ChecksConp`
- [ ] `zcBase` copies of the zp2 interpreter lemmas; `core` setup
- [ ] `fetch`, right move, `runFromC`, D used up
- [ ] DFS = ∃ (`pad` induction), `backtrack`, `searchC`
- [ ] dispatch, outer loop, `pair_mainConp`, `zconp_quasihalts_iff_sentence`
