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
