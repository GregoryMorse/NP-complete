# 02 — Z_PP (`native/zpp.py`, 295 states): `Quasihalts zppMachine ↔ SentencePP`

Prerequisite: plan 01 is done. This is the easiest machine and the template for the
others, so do it carefully and keep the file layout reusable.

**Difference from zp2.** The verifier phase also keeps an accept counter
`A = 1^(|s|+1)` after `C`:

    M_g J M_1 s M_2 C M_3 A M_4 fuel

- Every accepting certificate decrements `A`.
- When the decrement flips `A`'s leading (leftmost) bit, the truth is 1. That happens
  at the 2^|s|-th accept.
- If `C` underflows first, the truth is 0.

It changes 3 zp2 states (DP31, VFE, BD6) and adds 9.

## 1. Trusted definitions (`ZP/DefsPP.lean`, mirrors `ref/zpp_ref.py`)

```lean
/-- Number of accepting certificates of length |s|+1. -/
def accCount (s : List Bool) : Nat :=
  ((strings (s.length + 1)).filter fun c => run s c (s.length + 1)).length
def inPP (s : List Bool) : Bool := decide (2 ^ (s.length + 1) ≤ 2 * accCount s)
def CorrectPP (J S : Nat) : Prop := run (str J) (str S) (clock (str J) (str S)) = inPP (str S)
instance : ∀ J S, Decidable (CorrectPP J S) := …
def SentencePP : Prop := ∃ J, 1 ≤ J ∧ ∀ S, 1 ≤ S → CorrectPP J S
```

Keep it literally as `ref/zpp_ref.py` reads (`2 * acc >= 2 ** (n + 1)`). Add
`decide` sanity checks in `ZP/ChecksPP.lean`:
- small `inPP (str k)` values, computed from `ref/zpp_ref.py`;
- the first two beeps of `zpp_ref.zp_beeps()`;
- `zppMachine.table.length = 295`.

`SentencePP` is `SentenceC (CorrectF inPP)` by `rfl`. State it that way so plan 01's
step H applies.

## 2. Generated files

```bash
cd /home/user/np-complete && python3 formal/gen_table.py zpp_native zppMachine && python3 formal/gen_logic.py zpp
```

The outputs are `ZP/TablePP.lean` and `ZP/LogicPP.lean`, the latter holding
`zppLogic`, `zppCert`, `namespace QPP`. (Check the exact table name in
`machines/`; `build.py` lists them.) Add both files to the CI diff step.

In `ZP/CompilePP.lean`:
```lean
theorem zppCert_ok : zppCert.OK := …                  -- decide +kernel, like zp2
theorem zpBase_ext_zpp : zpBase.Ext zppLogic := ext_of_extB (by decide +kernel)
```

## 3. The pair lemma (`ZP/PairPP.lean`)

Goal (same shape as `pair_main`, with `C := CorrectPP`):

```lean
theorem pairPP_main (J S : Nat) (hJ : 1 ≤ J) (hS : 1 ≤ S) : ∃ n, 0 < n ∧ Seg zppLogic (lay J S) n
    (lay (absStepC CorrectPP (J, S)).1 (absStepC CorrectPP (J, S)).2) (¬ CorrectPP J S)
```

Work out the phases on the Python machine first: run `native/zpp.py` on `J = '', s = '0'`
and print the tape at each visit of `GRB`, `GC`, `DP3*`, `AD`, `VA1`, `VF2`, `BD7`.

| phase | reuse | new |
|---|---|---|
| C build (`phase1`, `blkCopy`) | `zpBase` versions | — |
| A build | `BLK`/`COPY` loop lemmas (`copyLoop`, `blkCopy`) | the BD6→BN1 and BD7 dispatch segments |
| verifier fuel | as zp2 | the BD7→VG1 segment |
| one verifier run | `runFrom`, `setup`, `gcLoop`, `qcLoop` (all `zpBase`) | — |
| accept | — | segments `DP31→DPA1→DPA2→AD` (decrement A), `ACHK→ALB→VN2` (then C -= 1 as zp2), `ACHK→ALC→VA1` (truth 1) |
| reject | zp2's `VN1/VN2` path, but the refill now skips A (`VFE→VFA→VF2`) | the VFE/VFA segments |
| truth flag → `TR j Sb b` | — | check that the A block is erased so the tape is **exactly** zp2's `TR`; if not, define `TRPP` and redo `dPhase`'s first segment |
| decider + compare + successor | `dPhase`, `dOk*`, `dBad*`, `sincL`, `jincL`, `beepStep` via `Ext` | — |

Use `symexec.py --logic ZP/LogicPP.lean` (from plan 01) to design each new segment.

### The counting invariant (the only real math)

Generalize `vLoop` (`ZP/Pair.lean:893`) with an accept count `a`:

```lean
def GCvPP (j : List Nat) (Sb cl : List Bool) (a : Nat) : ZC   -- A holds 2^(n+1)-1-a, n+1 bits, MSB left
theorem vLoopPP (j) (hj : Bits j) (Sb) : ∀ N cl a, bv cl = N → cl.length = Sb.length + 1 →
    a < 2 ^ Sb.length →
    a = accAbove Sb cl →          -- # accepting c with bv c > bv cl
    ∃ b, (b = true ↔ 2 ^ Sb.length ≤ accAbove Sb cl + accUpTo Sb cl) ∧
      zppLogic.Reach (GCvPP j Sb cl a) (TR j Sb b)
```

Induction on `N` follows the shape of `vLoop`.

**Arithmetic on A.** Write A's bits MSB first with `bitsOf (ofNatW (n+1) v)`. Prove:
- decrementing `v > 0` flips the leading bit iff `v = 2^n`;
- `v = 2^(n+1)-1-a` with `a < 2^n` gives `v ≥ 2^n`.

**Bridge to `accCount`.** Prove
`accCount s = #{v < 2^(n+1) | run s (ofBv v).reverse (n+1)}`. Do it by induction on the
length, through a lemma

```lean
((strings (k+1)).filter P).length
  = ((strings k).filter (P ∘ (false :: ·))).length + ((strings k).filter (P ∘ (true :: ·))).length
```

(`strings` is a `flatMap`, so use `List.filter_flatMap`/`List.length_flatMap`). Put this
generic counting library in `ZP/Count.lean`; plan 06 (PSPACE) reuses
`ofBv`/`bv`. `vFull` (`ZP/Pair.lean:943`) shows how zp2 bridges `∃` over `strings`
to the `bv` order, so copy that structure.

## 4. Top level

```lean
-- ZP/LogicalPP.lean
theorem zppLogic_macroSim : Nonempty (LMacroSimC CorrectPP zppLogic) :=
  lmacroSim_of_pairs zppLogic CorrectPP lay 2 rfl pairPP_main
theorem zpp_quasihalts_iff_sentence : Quasihalts zppMachine ↔ SentencePP
theorem zpp_quasihalts_iff_InP : Quasihalts zppMachine ↔ InP (fun s => inPP s = true)  -- plan 01 step H
```

Check `zconf 2 = lay 1 1` for zpp; the start path is unchanged from zp2, so `rfl`
should work.

Add `ZP.zpp_quasihalts_iff_sentence` to `Challenge.lean` (with `sorry`), to
`Solution.lean`, and to `comparator.json`. Add the new trusted files (`DefsPP`,
`TablePP`) to the trusted-surface list in `Challenge.lean`'s docstring and in
`formal/README.md`.

## 5. Optional, later: `SentencePP ↔ P = PP`

This is the analogue of `Hard.lean`. It needs:
- a definition of PP (`#acc ≥ half` with polynomial verifiers) in `Complexity.lean`;
- a proof that `inPP` is PP-complete under the padding reduction. The reduction must
  preserve the *count* of accepting certificates, up to the factor that sets the
  threshold.

Our `DX` construction is not parsimonious, because certificate padding multiplies the
count by 2^(pad bits). Only start this after every machine has its quasihalting
theorem, and write a design note before any Lean.

## Estimate

~1500–2500 new lines: 300 Defs/Checks, ~1000 segments and loops, ~400 counting library.

## Status: DONE

Files: `ZP/DefsPP`, `ChecksPP`, `TablePP`, `LogicPP`, `CompilePP`, `Count`, `PairPP`, `MainPP`.
Theorems: `ZP.zppQuasihalts_iff_sentence : Quasihalts zppMachine ↔ SentencePP` (also in
`Challenge/Solution/comparator.json`) and `ZP.zpp_quasihalts_iff_InP`.

**How it was done (the recipe for the other zp2-guest machines, plans 03, 04, 05, 06):**

1. `PairPP.lean` started as a *copy* of the `zpLogic`-dependent blocks of `Pair.lean` in
   `namespace ZP.PP` with `zpLogic → zppLogic`, `Correct → CorrectPP`, `inL → inPP`.
   `decide +kernel` re-checks every segment against the new machine; only the lemmas that
   touch changed transitions fail (here `blkVer`, `vAcc`, `vRej*`).
2. Failing/new segments were generated by `/tmp`-style scripts around
   `formal/scripts/symexec.py` (`LOGIC=LogicPP LOGICID=zpp`): describe start/end `SC`s, get the
   fuel with `reachN`, emit `checkFF … (by decide +kernel)`. Statement + proof of ~12 segments
   (`rejE rejC accEnt accCnt accUnt accThr1 accThr2 blkA blkVerPP …`) are produced by looping
   over the symbol parameters.
3. Glue: `phase1PP`, `vStartPP`, `runPP` (reuses `runFrom` with `A` in the work area `W`),
   `vStepPP`, `vLoopPP`, `vFullPP`, `pair_mainPP`.
4. `Count.lean`: `T`, `T_range`, `T_rev`, `ofBv`, `psum` — sums over `strings k` as sums over
   numbers; reusable.
5. `MainPP.lean`: `PairData`, `zppPairData.macroSim`, then the generic bridge and
   `sentenceF_iff_InP`.
