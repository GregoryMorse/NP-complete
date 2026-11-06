# 05 — Z_GI (`native/zgi.py`, 415 states): `Quasihalts zgiMachine ↔ SentenceG`

Prerequisite: plan 03 (`GlueF`: new instance, copy, result path, decider, successors).
zgi drops zfac's conversion and divisibility loops (`DROP` in `zgi.py`) and has no
binary conversion. The reversed copy of `s` just has its 0s turned into separators,
so the copy *is* the list of unary run lengths.

This is the hardest of the zp2-guest machines, because the search is over all
injective maps.

## 1. Trusted definitions (`ZP/DefsG.lean`, mirrors `ref/zgi_ref.py`)

Mirror `parse`, `check` and `in_LG` literally:
- runs: `s` split at `false`, lengths, reversed;
- `m := T[0]`;
- `X` = the runs before the first `0` in `rest`;
- `H` = the runs before the next `0`.

Define `injMaps m t : List (List Nat)` = all injective `w : Fin t → {1..m}` as lists.
Any enumeration works, because `inLG` uses `List.any` (existence). So choose the one
that makes the machine proof easiest: **the machine's own order** (push `m`,
decrement past collisions, pop when empty). The trusted definition can still be the
simple one (`permutations`-like: all length-`t` lists over `1..m` without
duplicates, `t ≤ m`), as long as you then prove:

```lean
theorem machineOrder_complete : w ∈ machineOrder m ↔ (w.Nodup ∧ w.length ≤ m ∧ ∀ v ∈ w, 1 ≤ v ∧ v ≤ m)
```

`check w m X H` mirrors the ref:
- `X` has even length;
- for each edge `(x, y)`: the labels are ≤ |w|, `k = (w[x-1]-1)*m + w[y-1]` satisfies
  `k ≤ |H|`, `H[k-1] ≥ 2`, and the `k` are pairwise distinct;
- every `k` with `H[k-1] ≥ 2` is used.

Add `decide` checks against the ref on ~40 small strings (keep `m ≤ 3`) and the first
beeps.

## 2. Generated files

Run:
- `gen_table.py zgi_native zgiMachine`;
- `gen_logic.py zgi`, with parent zfac.

Prove `zfGlue.Ext zgiLogic` (37 glue transitions shared; measured).

## 3. Phases (Python trace on tiny graphs first: m = 2, one edge)

1. **Setup** (`TS gTC gUP`). Turn the reversed copy into `B w M .. M M m M X .. MM H ..`.
   Lemma: the tape after setup is `unaryList (runs s)` with separators.
2. **Search** (`gPR gPR2 gPM …`).
   - The stack `w` sits at the left edge, each entry followed by its own `M`.
   - Push a copy of `m`. While the top equals another entry, decrement it. An emptied
     top is popped, and popping checks the stack below.
   - Spec: the machine checks exactly the injective `w` in `machineOrder m`, each once.
     Lemma by well-founded induction on a measure of the remaining search: the
     lexicographic position, or simply the count of remaining maps.
   - **Write the Python model of `machineOrder` first** and compare it with the
     machine's visited-`w` sequence on m ≤ 3 before writing Lean.
3. **Check one `w`** (`checkW`):
   - For an edge `(x, y)`, find `a = w_x` by marking one cell of `x` per skipped entry.
   - Row part: skip `m·(a−1)` entries of `H` (once per cell of `m`, one entry per cell
     of `a` but its last). An entry is skipped by marking its first cell.
   - Column part: skip `b − 1` more. Whether a row part is under way is read off
     `m`'s marks.
   - The entry reached must be an undeleted edge (≥ 2 cells, second cell unmarked). It
     is deleted by marking its second cell.
   - Finally every edge of `H` must be deleted.
   - Failure unmarks everything and decrements the top.
   - Lemmas:
     - `skipEntries n` (induction);
     - `findLabel x`;
     - `edgeStep`: one edge, success or failure;
     - `allDeleted`;
     - `checkW : … (check w m X H = true → reaches accept) ∧ (= false → reaches the decrement, tape restored)`.
   - "Tape restored" (all marks undone) is the invariant that makes the search
     induction work. State it explicitly.
4. **Result, decider, successors, top theorem**: plan 03, steps 4–6.
   ```lean
   theorem zgi_quasihalts_iff_sentence : Quasihalts zgiMachine ↔ SentenceG
   theorem zgi_quasihalts_iff_InP : Quasihalts zgiMachine ↔ InP (fun s => inLG s = true)
   ```

## Not in scope

`L_GI ≡_p GI` (the ref docstring's argument) stays on paper.

## Files

`DefsG`, `ChecksG`, `TableG`, `LogicG` (generated), `CompileG`, `SetupG`, `SearchG`,
`CheckG` (likely split in two; stay under ~1200 lines each), `PairG`.

## Estimate

~4000–5500 lines. Split the work into ≥ 3 sessions: (setup + search skeleton with
`checkW` sorried), (`checkW`), (glue + top).


## Status (in progress)

Done and building (no sorry), files `ZP/PairG.lean` and `ZP/SearchG.lean` (not yet imported by `ZP.lean`):
- shared decider/new-instance part copied for `zgiLogic`; `ni0`, `ni2a`, `gtcLoop` (setup: copy becomes `M ++ fz Xr`, entry `gUP`);
- push of a copy of `m` (`pushAll`), unmarking walks (`gupWalk`, `gflWalk`), the pairwise collision scan of the top against
  one entry (`cmpAll`) and against all entries (`scanLoop`), `failPath`, pop/decrement/empty-stack lemmas;
- abstract DFS (`Rch`, `Expl`, `Rch_sem`, `Rch_total`) and the machine lemma `GEnv.search_machine`, parameterised by
  `CheckSpec` (the check phase).

Still to do: (1) `CheckSpec` (states `gGL gUW gUW2 gXm gY1* gLP* gLW* gM1 gIL* gN* gS3 gS4 gD* gTR* gN2c/d gHU* gHC gFN*`
and `gFG`); (2) the link `Rch [] m b` <-> `inLG` (via `Expl` and `injL`); (3) the truth phase wrapper
(entry `gUP` -> result `FR0/FE/FR1`), `newInstG`, `pair_mainG`, `MainG`, Challenge/Solution/comparator entries.
Key tape facts: the stack is stored top-first as `Enc rest` (`U v = 1^v M`), so the check word is `rest` itself;
`good s := checkG s m X H`.

### Status update (check phase, `ZP/CheckG*.lean`, all building, no `sorry`, not yet imported by `ZP.lean`)

Done: `CheckG` (unmark walks, label find, inner-loop skeleton, reset walks), `CheckG2` (row loop in the
`MP/MU` form, column part, `huWalk`), `CheckG3`:
- `HP`, `HFam` (a family of `H` tapes indexed by the number of passed entries, with a tail `J` of shape
  `[]`, `[1]` or `1 :: 1 :: _` after the last entry, then the blank and `Zt`), `HFam.ofHP`;
- success: `innerLoopU`/`innerLoopU0`, `rowIterU`, `rowLoopU`, `colPre`, `colPartU`, `edgeRow` (label found -> end of row
  loop), `toY1`/`toY1g` (back to the start of `X`);
- failure (`FailsTo c U Z`: reach `hdR gFG A (R1 ++ 0 :: Z)` with `unm (A ++ R1) = U`): `hSkipFail`, `innerLoopF`,
  `rowIterF`, `rowLoopF`, `colPartF1`, `colPartF2`/`huFail`.
The H tape of the machine is NOT terminated by an `M` in general, so the success lemmas of `CheckG2` that use
`MP pasT ++ MU HU ++ Rt` cannot reach the last entry; use the `HFam` versions.

Still to do: `labelFail` (x or y > |w|), odd `X`, the glue `labelFind -> gIL0 -> colPartU -> toY1g`, the edge-loop
induction against `checkEdges` (H state `HP (Hs H used) 0 ++ J`), the final check `gFN*`, `CheckSpec` (via `failPath`), the link
`Rch` <-> `inLG`, the truth-phase wrapper, `pair_mainG`, `MainG`, entries, import in `ZP.lean`.


### Status update (CheckG3/4/5, all building, no `sorry`, not yet imported by `ZP.lean`)

Check phase for a **nonempty `H`** is complete end to end:
- `CheckG3`: success path for every edge (`edgeStep`, `loopOk`), final check (`finalOk`/`finalBad`), failure
  families `labelFindF`, `rowFail`, `rowNoTarget`, `colNoTarget`, `colPartF1/F2`.
- `CheckG4`: `firstFail`, `secondFail`, `edgeFailF`, `hsBad` (the `R0` shapes at the target), `edgeFail`,
  `loopFail` (any `X`), `oddFail`/`loopOdd` (lone last label, gadget `y1oEnd`), `finalAcc`, `finalFail`,
  and `checkAFull`: accepts iff `checkG`, else `FailsTo` the unmarked tape.
- `CheckG5`: `popE` (popped stack -> start of the edge loop, via `gglStart`/`phaseU`) and `checkSpecA`:
  `E.CheckSpec (fun w => checkG w (p+1) X H) AccS` whenever
  `E.Tc = rep (p+1) 3 ++ 1 :: (Enc X ++ 1 :: (HP (Hs H []) 0 ++ J))` with `JShape J`.

Still to do:
1. Degenerate tapes (`H = []`; `X` unterminated; `T = [m]`). `HFam` needs a nonempty `H`, so `H = []` needs an
   `N = 0` variant of the skip-failure walk (`hSkipFail0`, dispatch on `J0 ∈ {[], [1], 1::1::_}`).
   For `X = []` the machine accepts via `gY1e` on blank (`FE`), `gFN1` on blank/`M`. Plain `checkG` is true iff `X = []`.
2. The link `Rch [] m b <-> inLG` (via `Expl`, `injL`), including the parse/`Tc` shape lemma
   (`J` from the tail of `T`; `HP_Enc` gives `HP (Hs H []) 0 = (Enc H).dropLast`).
3. Truth-phase wrapper (`gUP` -> `FR0/FE/FR1`), `newInstG`, `pair_mainG`, `MainG`, entries; import in `ZP.lean`.

## Status update (CheckG6, after the separator refactor)

`HFam.Hc` now includes the separator `1` (so `Hc = []` means "no separator, no `H`"). The check phase is proved (CheckG3–CheckG6, no `sorry`, builds clean) for:
- non-empty `H`;
- `H = []` with a separator (including accept for `X = []`);
- `H` absent with no separator (S2, `Tc = rep m 3 ++ 1 :: Enc X`): `checkEmpty`/`checkSpecE` take `H0 = [] ∨ [1] ∨ 1::1::J'`, new `colPartF3`, `n2WalkNS`, `wn2WalkNS`, `y1oFail`, `y1eEndB`;
- `T = [m]` (`checkSpecS0`).

Open: S3, the unterminated tail (`Tc = rep m 3 ++ 1 :: (Enc X).dropLast`, `X ≠ []`, no `H`; must fail).
- `|X| >= 3`: the last entry fits `HFam` as an alternative `Hc 0 = rep k 3`.
- `|X| ∈ {1,2}`: the current label is the unterminated last one. Plan: generalise the label-level lemmas (`labelIterF`, `labelFindF`, `labelIter`, `labelFind`) from `1 :: (X0 ++ 0 :: Zt)` to a tail `Y ++ 0 :: Zt` so that `Y = []` is allowed, then add NS variants of `firstFail`/`secondFail`/`rowHalf` for that case.

Still to do after S3: shape case-split into `CheckSpec`, parse/`Tc` lemma, `Rch [] m b ↔ inLG`, truth-phase wrapper, `newInstG`/`MainG`, Challenge/Solution entries, import into `ZP.lean`. Plan 08 not started on `lean-n3-p08`; plan 07 skipped by instruction.

## Status update (CheckG8/CheckG9)
- `CheckG8`: unterminated-last-label variants (`Fmark`, `firstFailNS`, `secondFailNS`, `twoFailNS`) and
  `checkSpecS3` (|X| in {1,2}, last label unterminated). No `sorry`.
- `CheckG3/4/5/6`: `AccS E.Z` now carries `Z`, so the accepting `FE`/`FR1` configurations can be turned into `TR`.
- `CheckG9`: result paths `frPath0G`, `frPath1G`, `fePathG` (`FR0`/`FR1`/`FE` -> `hdR GRB ...`). No `sorry`.
- `m = 0` (last run of `s` empty): every `checkSpec*` lemma assumes `E.m = p+1`. Simulating `zgi.build()` from
  `CfgPop []` shows the machine does handle `m = 0` correctly (`checkG [] 0 X H = decide (X = [] ∧ no H entry >= 2)`):
  it takes `gGL gUW2 gXm(M) gY1e ...` and then either `gFN1` (X empty) or fails at the first label (`gLPe`/`gLW1`).
  A dedicated Lean lemma is still needed for this case.
- Still to do: `m = 0` lemma, parse/`Tc` lemma (`Tc = tcOfList (runsAux s 0).reverse`), shape case-split into
  `E.CheckSpec (fun w => checkG w (parseG s).1 ..) (AccS E.Z)`, truth-phase wrapper (`newInstG`), `layG`/`pair_mainG`,
  `MainG`, Challenge/Solution/comparator entries, imports in `ZP.lean` (files need module headers first).

## Status: done
`ZP.zgi_quasihalts_iff_sentence` (`Challenge.lean`/`Solution.lean`/`comparator.json`) and
`ZP.zgi_quasihalts_iff_InP` (`MainG.lean`) are proved with no `sorry`; they depend only on
`propext`, `Classical.choice`, `Quot.sound`. New in the last stretch: `CheckG10` (`m = 0`, via
`popM`, `finalAccM/FailM`, `firstFailM0T/U`, `checkSpecM0*`), `CheckG11` (`tcOfList`, `tc_runs`,
`csForm1..4`, `csList`, `csParse`), `CheckG12` (`genv_of`, `truthPhaseG`), `PairMainG`
(`newInstG`, `pair_mainG`), `MainG`. All files are `module` files and imported by `ZP.lean`.
