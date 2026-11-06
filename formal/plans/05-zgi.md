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
