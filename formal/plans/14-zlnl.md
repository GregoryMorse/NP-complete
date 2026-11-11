# 14 — Z_LNL (`native/zlnl.py`, 415 states): `Quasihalts zlnlMachine ↔ SentenceLNL`

Prerequisites: plan 13 (the multihead decider: `DefsMH`, `MHAct`, `MHRun`, `MHUnits`)
and the zp2 verifier development. This machine is zp2's verifier with a one-way head,
plus plan 13's decider.

Reference: `ref/znl_ref.py`; design: `docs/native.md` § "L = P and L = NL"; machine:
`native/zlnl.py` on top of `native/zmh.py` (182 logical states).

## 1. Trusted definitions (`ZP/DefsLNL.lean`, mirrors `ref/znl_ref.py`)

```lean
/-- zp2's run with a one-way head: d = 0 leaves the head in place. -/
def run1 (P x : List Bool) (T : Nat) : Bool       -- copy of runAux with `h` instead of `h - 1`
def inLNL (s : List Bool) : Prop := ∃ c ∈ strings (s.length + 1), run1 s c (s.length + 1) = true
def CorrectLNL (J S : Nat) : Prop := (runMH (str J) (str S) (clock (str J) (str S)) = true ↔ inLNL (str S))
def SentenceLNL : Prop := SentenceC CorrectLNL
```

`runMH` comes from plan 13's `DefsMH`. Checks: `run1` against `zp2_ref.run` on
programs that never move left (they agree), and on one that does (they differ);
`inLNL` on strings up to length 4 (`znl_ref.in_LNL`); the first 3 beeps.

## 2. Generated files and base

zlnl changes 13 zp2 transitions (`DG3,M`, `DW3,M`, `EAs,B`, `GH**,M`, `VG1,B`,
`VG3,M`, `WB3*,M`, `WC*,B`), adds 7 to zp2 states (`WC*` on `0 1 M`, `RGQ1,M`), removes
8 (`A`, `BB*`, `Y*`, `WB1`), and adds 59 states (plan 13's `zmh` states plus `XW*`,
`YW*`, `VGD`, `VGE`, `DG3V`, `GCD`). Unlike zlp it keeps zp2's certificate loop
(`VN*`, `VF2`, `VU2`), the guest-tape copy (`GC`, `GL*`, `GR*`, `GLM`), `WB2` (writes
`H`) and the halt (`GHH* EL* ER*`).

## 3. The one-way verifier

- **Setup.** `VG1 → VGD → VGE` writes `H` one cell further left and a dummy `0`
  between `H` and `M_g`; `VG3 → DG3V → GC` is zp2's guest copy of `C`, then zp2's code
  copy. Restate zp2's `setup` with the dummy cell; the countdown, fuel and peek lemmas
  only see `c_h` and `H`, so they carry over.
- **Act.** `GH wd → XW wd`: one look right of `H` (a bit: verifier). `XW w1 → YW w` is
  zp2's right move (`YW w,M → w, L, PUTH`). `XW w0 → WC w`: write `w` into `c_h` and
  **stay** (zmh's `WC w` skips `H` and writes at the blank `c_h`, then `RGQ1`). Prove
  the one-way step lemma: zp2's `segMv1` for `d = 1`, a short segment for `d = 0`.
- **Run lemma** `run1From`: zp2's `runFrom` with the new left move, result `run1`.
- **Halt**: zp2's `GHH`/`EL*`/`ER*` unchanged; the result dispatch's erase passes
  `EX` once (no storage: `EAs,B → EX`, `EX,B → EBs`).
- **Certificate loop**: zp2's `vLoop`/`vFull` unchanged (`∃ c`), with `run1` for `run`.

## 4. The decider

Plan 13's decider (`XW wd,M → G2 wd`: a decider run), with `zmh.units(t, 'UDW')`:
after each unit the head goes straight back to the walker (there are no verifier
units). Setup: zp2's `WB2` writes `H`, `DG3,M → GCD` skips `s` and blanks `M_2`, then
zp2's `GLM` and code copy (code `J`). Reuse `MHAct`, `MHRun` and `MHUnits` through
`Ext`; the storage is erased by `EAs,B → EX` (`zmh.erase`).

## 5. Pair lemma and top

`pairLNL_main`: zp2's verifier phase with `run1` (truth `inLNL`), then plan 13's
decider phase, compare, successor.

```lean
theorem zlnl_quasihalts_iff_sentence : Quasihalts zlnlMachine ↔ SentenceLNL
```

Add to `Challenge.lean`, `Solution.lean`, `comparator.json`.

"`SentenceLNL` ↔ L = NL" stays on paper: `L_NL ∈ NL` (guess the certificate on the
fly) and NL-hard (a program hard-wires a log-space NTM's configuration graph; the
certificate chooses the successors).

## Estimate

~2500–3500 lines on top of plan 13, 2–3 sessions: (1) defs, checks, base, one-way act
and run lemma; (2) setup with the dummy cell, decider reuse, pair lemma, top.

## Checklist

- [x] `DefsLNL` + `ChecksLNL`; generated files, certificate, base
- [x] one-way act, `run1I` (`LNLSeg`, `LNLRun`), halt without storage; decider engine `runMHIL` (`MHLRun`)
- [x] verifier setup with the dummy cell (`PairLNLSeg`, `PairLNLV`: `setupL`, `runFromL`, `vStepL`, `vLoopL`, `vFullL`, `vStartL`)
- [ ] decider via plan 13, `pairLNL_main`, `zlnl_quasihalts_iff_sentence`
