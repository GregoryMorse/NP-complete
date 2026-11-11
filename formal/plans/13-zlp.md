# 13 — Z_LP (`native/zlp.py`, 373 states): `Quasihalts zlpMachine ↔ SentenceLP`

Prerequisites: plan 01, and the lessons of plan 07 (a new guest model on the zp2
interpreter: the rotation, fuel and peek lemmas survive, the act and halt segments are
redone, and changed zp2 transitions need their own base). Plan 14 (L = NL) reuses
everything in §3–§4, so keep the multihead lemmas in their own files.

Reference: `ref/zmh_ref.py`; design: `docs/native.md` § "L = P and L = NL"; machine:
`native/zlp.py` on top of `native/zmh.py` (163 logical states).

## 1. Trusted definitions (`ZP/DefsMH.lean`, mirrors `ref/zmh_ref.py`)

```lean
structure MH where
  R : List Bool          -- rotated code
  pos : List Nat         -- head positions, |P| + 1 of them
  cur : Nat              -- current head
/-- the symbol at position p of ⊢x⊣: none at 0 and n+1 -/
def mhRead (x : List Bool) (p : Nat) : Option Bool := if p = 0 ∨ p = x.length + 1 then none else x[p-1]?
def runMH (P x : List Bool) (T : Nat) : Bool      -- literal copy of run_mh: rotate by iota,
                                                   -- T = 0 → false, peek w d t, t = 0 halts,
                                                   -- w = 1 moves pos[cur] (clamped to 0..n+1),
                                                   -- w = 0 moves cur (clamped to 0..|P|),
                                                   -- then rot and k+1 more rotations
def inLP (s : List Bool) : Bool := runMH s s (s.length + 1)
def CorrectLP (J S : Nat) : Prop := runMH (str J) (str S) (clock (str J) (str S)) = inLP (str S)
def SentenceLP : Prop := SentenceC CorrectLP
```

Mirror the ref's step order exactly: the time-out test comes after the ι rotations,
as in zp2's `runAux`. Store `pos` as a `List Nat` and update with `List.set`.
Checks (`ZP/ChecksMH.lean`, `decide`): `runMH` on hand-made programs that move a head
both ways and switch heads both ways (take them from `tests/test_native.py`'s
`test_multihead_instances`), `inLP` on strings up to length 4 (`zmh_ref.in_LP`), and
the first 3 beeps.

## 2. Generated files and base

```bash
python3 formal/gen_table.py zlp_native zlpMachine && python3 formal/gen_logic.py zlp
```

zlp changes 15 zp2 transitions (`BD6,M`, `DG3,M`, `DP30,0`, `DW3,M`, `EAs,B`,
`GH**,M`, `VA3,B`, `WB2,B`, `WB3*,M`, `WC*,B`), adds 7 to zp2 states (`WC*` on
`0 1 M`, `RGQ1,M`: zmh's carry into `c`), removes 62 (zp2's guest-tape act
`PUTH A BB* Y*`, the guest copy `GC GL* GR*`, the certificate loop `VN* VFE VF2 VU2`,
the verifier setup `VG1 VG2 VG3`, `WB1`, and cells that cannot occur: `EL2`, `GQ1`,
`PK1` on bits, `DP30/31,1`, `VA2,1`, `ER2*` on bits), and adds 54 states. Define
`zlBase` = `zpBase` minus the changed and removed transitions; what survives is the
rotation (`Rot.lean`), fuel (`Fuel.lean`), NAV/countdown/peek part of `Interp.lean`,
the halt `GHH* EL* ER*` (unchanged), the walker, `BLK`, and the `GLM GRM QN2 QC QE QE3`
code copy.

## 3. The multihead run (`ZP/MHStore.lean`, `ZP/MHAct.lean`, `ZP/MHRun.lean`)

Run layout (`docs/native.md`):

    Q gap c H M_g J M_1 s M_2 … fuel B storage

- `storeOf x pos cur` = concatenation over heads `i = k-1, …, 0` (head 0 is the last
  unit) of
  `(M :: x ++ [0]).take (pos i + 1) ++ [mark i] ++ (M :: x ++ [0]).drop (pos i + 1)`,
  with `mark i = B` if `i = cur`, else `M`.
- `c` holds `mhRead x (pos cur)` (as a cell: blank for `none`) at the start of a step.

Lemmas, each a `Seg` of `zlpLogic` (write them for an `Ext`-closed family so plan 14
can reuse them):

1. **Navigation.** From `GH wd,M` (`M_g` right of `H`), `G2 wd` skips to the blank
   after the fuel and `G3 wd` to the current marker (two "skip non-blank" loops).
   Needs: every cell between `H` and the fuel's end is non-blank, and the current
   marker is the first blank of the storage.
2. **The four ops.** `G3 11 → MR MR0 MR1` (right), `G3 10 → ML ML0 ML1` (left): swap
   the marker with the cell right / left of it; `G3 01 → LS1 LS3` (next head: the unit
   to the left), `G3 00 → RS1 RS3` (previous head: the unit to the right): the old
   marker becomes `M`, the neighbour's marker `B`. Each turns `storeOf x pos cur` into
   `storeOf x pos' cur'` with the ref's update. Prove each by a case split on the
   shape of the unit around the marker. Clamping: `MR` sees `M`/blank exactly at
   position `n + 1`; `ML` sees `M` exactly at position 0; `LS3` meets the blank left
   of the storage exactly at the first unit (back via `RS1`); `RS1` meets the blank
   right of the storage exactly at the last unit (back via `LS3`).
3. **Read and carry** (`RD RR RB1 RR2 RL KB K0 K1`, then zp2's `WC0 WC1` extended to
   skip non-blanks, and `RGQ1,M`): from the new current marker back to `c`, writing
   `mhRead x (pos' cur')`, then `RTW` at the gap.
4. **Step lemma** `mhStep`: one guest step = zp2's countdown on `c` (reuse: `c` plays
   the head cell), fuel decrement, peek, act (2.–3.), recording rotation and the token
   rotations (reuse). Halt: zp2's `GHH w` writes the outcome into `H` and `EL*`/`ER*`
   erase the left side unchanged (the storage lies right of the fuel and stays).
5. **Run lemma** `mhRunFrom`: induction on the fuel, like zp2's `runFrom`, giving
   `runMH P x T` at the result dispatch with the storage still at the far right. It is
   erased by the far-right erase loops (`EAs,B → EX`, `VA3,B → EY`: `zmh.erase`).

The decider runs **any** code `J` on `s` with `|J| + 1` heads. The test
`test_multihead_act` checks items 2–3 (from `G2 wd` right of `H` to `RTW`) on every
storage with `|x| ≤ 3` and up to 3 heads. Use it to pin the exact statements before
proving them.

## 4. Building the storage (`ZP/MHUnits.lean`)

- **Unit append** (`U0 U1 U2 U5 U6 UB2 UB3 UCP UC* UC2* UK* UK2* UE1 UE2 V UL1 UL2`):
  from left of the fuel's end, `U1`/`U2` turn the old current marker into `M` and
  write the new unit's `M` and marker; `U5 U6 UB2 UB3` go back to `s` (between `M_1`
  and `M_2`); the copy loop over `s` uses the blank-and-restore pattern of `BLK`;
  `UE1 UE2` write the final `0`, `V` makes the new marker current; `UL1 UL2` return to
  the far left. One lemma, parametrized by what lies left of the fuel.
- **Decider:** the walker. `DW3,M → U0` (walker at `M_1`), `WB3 j,M → U0` (each step
  back), and `UDW` returns to the walker. Result: `|J| + 1` units, the last current.
  Restate zp2's `walkBack` with the unit appended per step; `WB2,B → DG2` ends at home
  without writing `H`.
- **Dispatch and verifier units** (`DG3,M → GCD → GC2`): `GCD` skips `s`, `GC2` reads
  the field after `M_2`. `M` (the decider's truth flag): decider. A bit: `C =
  1^(|s|+1)` (zp2's `BLK`; `BD6,M → UL2` then returns home): `GC2`/`GC4` turn the
  first `1` into `0` and append a unit (`→ U0`, back through `UDW` and the dispatch)
  until `C` is all 0s: verifier.
- **Setup:** `GC2,M → GC4` blanks `M_2` (decider, code `J`), `GC4,M` blanks the `M`
  after `C` (verifier, code `s`); `GLMD` writes `H` left of `M_g`; then zp2's `GLM`
  (placeholder `c`) and code copy `GRM QN2 QC QE QE3`.

## 5. Pair lemma and top (`ZP/PairLP.lean`, `ZP/MainLP.lean`)

Verifier: `C` and verifier fuel (zp2's `BLK`), units from `C`, one run of `s` on `s`,
`DP31` / `DP30,0` write the truth flag `M 1` / `M` (`VA2 VA3 VA4 FB`, storage erased
by `EY`). Decider: walker fuel with units, run of `J` on `s`, compare (`DP4*`), erase
(`EAs EX EBs`), successor (zp2). Then
`lmacroSim_of_pairs` and

```lean
theorem zlp_quasihalts_iff_sentence : Quasihalts zlpMachine ↔ SentenceLP
```

Add to `Challenge.lean`, `Solution.lean`, `comparator.json` (`ZP.DefsMH`, `ZP.DefsLP`,
`ZP.TableLP`).

"`SentenceLP` ↔ L = P" stays on paper: multihead DFAs = log space (Hartmanis), and
`L_P` is P-complete under log-space reductions (heads as tape cells, padding). A Lean
version needs log-space machines and reductions; out of scope.

## Estimate

~5000–7000 lines, 4–5 sessions: (1) defs, checks, base; (2) store invariants, the four
ops, read/carry; (3) step and run lemmas; (4) unit append, walker with units, verifier
units, setup; (5) pair lemma, top.

## Checklist

- [x] `DefsMH` + `DefsLP` + `ChecksLP`; AllDefs/Challenge regenerated (commit 19851ca)
- [x] shared numbering (`QMH`, 50 core states), `LogicBaseMH.mhBase`, `ExtChecksMH`
      (`mhBase_ext_zlpLogic`, `mhBase_ext_zlnlLogic`); zlnl regenerated on the same numbering
- [x] `MHRot`, `MHFuel`, `MHInterp` (retargeted from zp2, Lw-free), `MHSeg` (generated by
      `scripts/gen_mhinterp.py`: `segA0`, `segExh0`, `segHalt`, `segShort1`, `segShort2`, `segPk`)
- [x] `MHStore` (`storeOf x pos cur`, `Sym4`/`NoB` facts, `cellN_mhRead`), `MHActSeg` (generated,
      `scripts/gen_mhact.py`) + `MHAct` (`act`: G2 w d -> RTW over `storeOf`, `actPos`/`actCur`),
      `MHRunSeg` (`segC0`) + `MHRun` (commit 785be60): `peek`, `dec`, `countdown`, and
      `runMHI L hext hGH x W hW np T R g pos cur ds ...`: from `Bd R g (mhRead x p) (1::(W++1::FWr ds))
      (0::storeOf x pos cur)` to `RE (runMHAux np x T R pos cur) (W++1::(FWr ds'++0::storeOf ..))`
      for any L with `mhBase.Ext L` and `GHStep L` (GH w d,M -> G2 w d). Shared with plan 14.
- [x] `MHUnitSeg` (generated) + `MHUnits` part 1 (commit d8b3004): `ustoreN x k`, `unitApp`, `walkUnits`
- [ ] `MHUnits` part 2: shared `decFuel` with units (mhBase), zlp-only generated segments (UDW->GC2 dispatch,
      gcStep, verifier/decider ends, glmEnd, post-run DP, VA3/EY erase), setup lemma (GLMD..segB),
      verifier chain over `runMHI`, dPhase, compare/erase/successor phases
- [ ] `PairLP` (pair lemma), `MainLP` (`zlpQuasihalts_iff_sentence`), Challenge/Solution/comparator
- Tools: `scripts/seggen.py` emits checkTT/TF/FT/FF segment lemmas with auto-found fuel
  (see `gen_mhinterp.py` for usage); `scripts/symexec.py` takes `ROWS`/`QFILES` env vars.
