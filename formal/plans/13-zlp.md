# 13 — Z_LP (`native/zlp.py`, 426 states): `Quasihalts zlpMachine ↔ SentenceLP`

Prerequisites: plan 01, and the lessons of plan 07 (a new guest model on the zp2
interpreter: the rotation, fuel and peek lemmas survive, the act and halt segments are
redone, and changed zp2 transitions need their own base). Plan 14 (L = NL) reuses
everything in §3–§4, so keep the multihead lemmas in their own files.

Reference: `ref/zmh_ref.py`; design: `docs/native.md` § "L = P and L = NL"; machine:
`native/zlp.py` on top of `native/zmh.py` (191 logical states).

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

zlp changes 13 zp2 transitions (`BD6,M`, `DG3,M`, `DP30,0`, `DW3,M`, `GH**,M`,
`GHH*,M`, `QE3,M`, `WB3*,M`), removes 64 (zp2's guest-tape act `PUTH WC* A BB* Y*
RGQ1`, the guest copy `GC GL* GR* GLM`, the certificate loop `VN* VFE VF2 VU2`, `WB1`,
`EL1`, and cells that cannot occur: `EL2`, `GQ1`, `PK1` on bits, `DP30/31,1`, `VA2,1`,
`ER2*` on bits), and adds 84 states. Define `zlBase` = `zpBase` minus the changed and
removed transitions; what survives is the rotation (`Rot.lean`), fuel (`Fuel.lean`),
NAV/countdown/peek part of `Interp.lean`, the walker, `BLK`, and the `QN2/QC/QE` code
copy.

## 3. The multihead run (`ZP/MHStore.lean`, `ZP/MHAct.lean`, `ZP/MHRun.lean`)

Run layout (`docs/native.md`):

    Q gap c H M_g J M_1 s M_2 … fuel B storage

- `storeOf x pos cur` = concatenation over heads `i` of
  `M M (0 :: x ++ [0]).take (pos i + 1) ++ [mark i] ++ (0 :: x ++ [0]).drop (pos i + 1)`,
  with `mark i = B` if `i = cur`, else `M`.
- `c` holds `mhRead x (pos cur)` (as a cell: blank for `none`) at the start of a step.

Lemmas, each a `Seg` of `zlpLogic` (write them for an `Ext`-closed family so plan 14
can reuse them):

1. **Navigation.** From `GH wd` at `H`, the machine reaches the current marker
   (`G2`, `G3`: two "skip non-blank" loops). Needs: every cell between `H` and the
   separator is non-blank, and the current marker is the first blank of the storage.
2. **The four ops** (`MR*`, `ML*`, `NX*`, `NXB`, `PV*`). Each turns
   `storeOf x pos cur` into `storeOf x pos' cur'` with the ref's update. Prove each by
   a case split on the shape of the unit around the marker. Clamping: `MR2` sees
   `M`/blank exactly at position `n + 1`; `ML2` sees `M` exactly at position 0; `NX1`
   reaches the storage end exactly at the last unit; `PV3` reaches the separator
   exactly at the first.
3. **Read and carry** (`RD RR RB1 RR2 RL1 RL2 RL4 K* K2*`): from the new current marker
   back to `c`, writing `mhRead x (pos' cur')`, then `RTW` at the gap.
4. **Step lemma** `mhStep`: one guest step = zp2's countdown on `c` (reuse: `c` plays
   the head cell), fuel decrement, peek, act (2.–3.), recording rotation and the token
   rotations (reuse). Halt: `GHH w` writes the outcome into `H`, then
   `ESP ES1 ES2 ESB ESN` erase the storage and join zp2's `EL2` erase.
5. **Run lemma** `mhRunFrom`: induction on the fuel, like zp2's `runFrom`, giving
   `runMH P x T` at the result dispatch with the storage erased.

The decider runs **any** code `J` on `s` with `|J| + 1` heads. The test
`test_multihead_act` checks items 2–3 on every storage with `|x| ≤ 3` and up to 3 heads.
Use it to pin the exact statements before proving them.

## 4. Building the storage (`ZP/MHUnits.lean`)

- **Unit append** (`U0 … UE2`): appends `M M 0 M s 0` at the far right (copy loop over
  `s` with the blank-and-restore pattern of `BLK`), then returns to the far left
  (`UL1 UL2`). One lemma, parametrized by what lies left of the fuel.
- **Decider:** the walker. `DW3,M → U0` (walker at `M_1`), `WB3 j,M → U0` (each step
  back), and `UDW` returns to the walker. Result: `|J| + 1` units. Restate zp2's
  `walkBack` with the unit appended per step.
- **Verifier:** `BD6,M → UCL → UD`: one unit per cell of `C = 1^(|s|+1)`, consumed to
  0s (`UD`, `UD2`), and `UF1–UF3` read the field after `M_2` to dispatch (bit: `C`,
  `M`: decider). `UD2,M → VG1`.
- **Setup** (`GCD S1 S2 S5 S6 S7 GLMD GLM2`, `QE3`, `QE4`): first marker current, `c`
  placeholder and gap separator left of `H`, then zp2's code copy (`GRM QN2 QC QE`)
  with code `J` (decider) or `s` (verifier).

## 5. Pair lemma and top (`ZP/PairLP.lean`, `ZP/MainLP.lean`)

Verifier: `C` and verifier fuel (zp2's `BLK`), units from `C`, one run of `s` on `s`,
`DP31` / `DP30,0` write the truth flag `M 1` / `M` (`VA2 VA3 VA4 FB`). Decider: walker
fuel with units, run of `J` on `s`, compare (`DP4*`), successor (zp2). Then
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

- [ ] `DefsMH` + `ChecksMH`; generated files, certificate, `zlBase`
- [ ] `storeOf`, navigation, the four ops (`MHAct`)
- [ ] read/carry, `mhStep`, `mhRunFrom` (`MHRun`)
- [ ] unit append, walker units, verifier units, setup (`MHUnits`)
- [ ] `pairLP_main`, `zlp_quasihalts_iff_sentence`, Challenge/Solution
