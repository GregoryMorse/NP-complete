# 11 — Z_BPP (`native/zbpp.py`, 333 states): `Quasihalts zbppMachine ↔ SentenceBPP`

Prerequisites: plan 01 (generic pipeline) and plan 02 (Z_PP): this machine is Z_PP with
two counters instead of one, and reuses `ZP/Count.lean` (`accCount`, `bv`, `ofBv`,
`accAbove`/`accUpTo`) and the shape of `vLoopPP`.

Reference: `ref/zbpp_ref.py`; design: `docs/native.md` § "Promise-P = promise-BPP";
machine: `native/zbpp.py` (152 logical states).

**Difference from zp2.** The verifier phase keeps an accept counter `A` and a reject
counter `R` after `C`:

    M_g J M_1 s M_2 C M_3 A M_4 R M_5 fuel

- `A` and `R` start at `⌈3N/4⌉ − 1` with `N = 2^(|s|+1)`: `1^(|s|+1)` with the second
  cell turned 0 (`1` for `|s| = 0`).
- An accepting certificate decrements `A`, a rejecting one `R`; then `C` is decremented
  as in zp2.
- A borrow out of `A`'s leading bit (the `⌈3N/4⌉`-th accept) ends the phase with truth 1,
  one out of `R` with truth 0.
- If `C` underflows first, `s` is **outside the promise**: everything right of `M_2` is
  erased and the machine moves to `s + 1` without running `J`.

## 1. Trusted definitions (`ZP/DefsBPP.lean`, mirrors `ref/zbpp_ref.py`)

```lean
/-- `some true` (YES: 4 acc ≥ 3N), `some false` (NO: 4 rej ≥ 3N), `none` (outside). -/
def capp (s : List Bool) : Option Bool :=
  let N := 2 ^ (s.length + 1)
  let acc := accCount s                       -- from DefsPP
  if 3 * N ≤ 4 * acc then some true
  else if 3 * N ≤ 4 * (N - acc) then some false else none
def CorrectBPP (J S : Nat) : Prop :=
  match capp (str S) with
  | none => True
  | some t => run (str J) (str S) (clock (str J) (str S)) = t
instance : ∀ J S, Decidable (CorrectBPP J S) := …
def SentenceBPP : Prop := SentenceC CorrectBPP
```

Keep the order of the two tests as in the ref (YES first). Both cannot hold, since
`3N ≤ 4 acc` and `3N ≤ 4 (N − acc)` sum to `6N ≤ 4N`. Prove that as a lemma, since the
machine decides by whichever counter borrows first.

Checks (`ZP/ChecksBPP.lean`, `decide`): `capp` on the first ~30 strings (values from
`zbpp_ref.capp`; 18 of the 63 strings up to length 5 are outside the promise), the
first 3 beeps of `zbpp_ref.zp_beeps()`, the table length.

## 2. Generated files

```bash
python3 formal/gen_table.py zbpp_native zbppMachine && python3 formal/gen_logic.py zbpp
```

`ZP/TableBPP.lean`, `ZP/LogicBPP.lean`; `zbppCert_ok` by `decide +kernel`. zbpp changes
8 zp2 transitions (`DP31` and `DP30` on bits, `VN2,M`, `VFE,M`, `BD6` on `B` and `M`),
adds `CX,0` (C, A, R may hold 0s when a block is appended) and 23 states (`DPA*`, `AD`,
`ALB`, `ALC`, `VA1`, `DPR*`, `RD`, `RLB`, `RLC`, `RLD`, `VFA`, `VFR`, `BD7`, `BD8`,
`FXA*`, `FXR*`). If any changed transition is in `zpBase`, define `zbBase` = `zpBase`
minus those, as in plan 07, and retarget the surviving zp2 lemmas.

## 3. Phases

Print the tape on the Python machine at `GRB`, `BD6`, `BD7`, `BD8`, `FXA2`, `FXR2`,
`VG1`, `DP3*`, `AD`, `RD`, `VN2`, `VF2`, `EAs` for `J = ''` and `s ∈ {'', '0', '0001'}`
(`'0001'` is outside the promise) before writing statements.

| phase | reuse | new |
|---|---|---|
| C build, A build, R build | `blkCopy`, the BD dispatch of plan 02 | `BD7`/`BD8` dispatch; `FXA`/`FXR`: turn the second cell of a fresh `1^(n+1)` block into 0 |
| verifier fuel, one run | zp2 (`runFrom`, `setup`, copy loops) | — |
| accept | plan 02's `DP31 → DPA → AD` | `AD` underflow `ALC → VA1` (truth 1) |
| reject | — | `DP30 → DPR1..3 → RD`; underflow `RLC → RLD → VU2` (truth 0); else `RLB → ALB → VN2` |
| C decrement | zp2 `VN2`, refill `VFE → VFA → VFR → VF2` | the skips over `A`, `R` |
| C underflow | — | `VN2,M → EAs`: erase right of `M_2`, `s + 1` (outside the promise) |
| decider, compare, successor | `dPhase`, `dOk*`, `dBad*`, `sincL`, `jincL`, `beepStep` | — |

### The counting invariant

Generalize `vLoopPP` with both counts: after the certificates with `bv c > bv cl`,
`A = a0 − acc` and `R = a0 − rej` (`a0 = ⌈3N/4⌉ − 1`), both nonnegative, where
`acc + rej` = number of certificates done. A borrow out of `A` happens exactly when
`acc` reaches `a0 + 1 = ⌈3N/4⌉`, i.e. when `4 acc ≥ 3N` first holds. Result:

```lean
theorem vLoopBPP … : ∃ r : Option Bool, r = cappPrefix … ∧ zbppLogic.Reach (GCvB …) (outcome r)
```

with `outcome (some b)` = zp2's `TR j Sb b` and `outcome none` = the `EAs` entry of the
outside branch. Bridge `cappPrefix` at the last certificate to `capp` with plan 02's
`accCount` lemmas. **Arithmetic.** `⌈3N/4⌉ − 1` in binary is `1 0 1^(n−1)` for
`n ≥ 1` (`N = 2^(n+1)`, so `3N/4 = 3·2^(n−1)`): prove `bitsOf (ofNatW (n+1) (3·2^(n−1) − 1))
= true :: false :: replicate (n−1) true`.

## 4. Pair lemma and top

`pairBPP_main J S`: three outcomes. YES/NO: decider phase as zp2, beep iff
`¬ CorrectBPP`. Outside: no decider run, straight to `(J, S+1)`, which is
`absStepC CorrectBPP (J, S)` because `CorrectBPP J S` holds. Then
`lmacroSim_of_pairs`, `zbppMacroSimC`, and

```lean
theorem zbpp_quasihalts_iff_sentence : Quasihalts zbppMachine ↔ SentenceBPP
```

Add to `Challenge.lean`, `Solution.lean`, `comparator.json` (`ZP.DefsBPP`, `ZP.TableBPP`).

"`SentenceBPP` ↔ promise-P = promise-BPP" stays on paper (`docs/native.md`). It needs
promise classes, the padding reduction and error amplification; write a design note
before any Lean.

## Estimate

~2000–3000 lines, 2 sessions: (1) defs, checks, generated files, the A/R build and
dispatch segments; (2) the two-counter invariant, the three outcomes, pair lemma, top.

## Checklist

- [x] `DefsBPP` + `ChecksBPP`; generated files, certificate (`gen_logic.py zbpp`, `gen_table.py zbpp_native`)
- [x] A/R build (`blkA0/1/2`, `blkR0/1/2`, `blkVerBPP`; three cases because the second cell is fixed)
- [x] accept/reject/decrement segments, outside-the-promise branch (`accTrue1/2`, `rejTrue`, `accDecE/C`,
  `rejDecE/C`, `accOut`, `rejOut`; each generated from `scripts/symexec.py`)
- [x] two-counter `vLoopBPP` (counters hold the remaining allowed accepts/rejects as numbers), bridge to
  `capp` (`capp_eq`, `thr_excl`, `vFullBPP`)
- [x] `pair_mainBPP`, `zbpp_quasihalts_iff_sentence`, Challenge/Solution/comparator

Done in one session. Deviations from the plan: no `zbBase` was needed (`zpBase` is contained in
`zbppLogic`: `zpBase_ext_zbppLogic`); the copy lemmas of `PairPP` were generalized from `O13` to
`NB` because the copied area now contains 0s; the counters are decremented as numbers (initial
value `thrN n`), not compared with a leading-bit test, so the invariant is
`¬(a < acc ∧ r < rej)` and the result is `some true ↔ a < acc`, `some false ↔ r < rej`.
