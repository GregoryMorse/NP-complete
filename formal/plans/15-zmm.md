# 15 — Z_MATMUL (`native/zmm.py`, 494 states): `Quasihalts zmmMachine ↔ SentenceMM`

Prerequisites: plan 07 (Z_MUL, done). This machine **is** Z_MUL with a new output
check: the guest model, fuel, switch, run theorem, setup and dispatch are Z_MUL's.
Only the check after a proper halt changes. So the work is (a) making the Z_MUL
lemmas usable from a second machine and (b) one new check routine.

Reference: `ref/zmm_ref.py`; design: `docs/native.md` § "Linear-time GF(2) matrix
product"; machine: `native/zmm.py` (212 logical states: zmul minus its check, plus 70
check states).

## 1. Trusted definitions (`ZP/DefsMM.lean`, mirrors `ref/zmm_ref.py`)

```lean
/-- s = 1^m 0 w: m, then B = w[0:m²] padded, A = w[m²:] in rows of length m. -/
def mmM (s : List Bool) : Nat := (s.takeWhile id).length
def mmW (s : List Bool) : List Bool := s.drop (mmM s + 1)
def padTo (n : Nat) (l : List Bool) : List Bool := (l ++ List.replicate n false).take n
def mmB (s : List Bool) (k j : Nat) : Bool := (padTo (mmM s ^ 2) (mmW s)).getD (k * mmM s + j) false
def mmRows (s : List Bool) : Nat := if mmM s = 0 then 0 else ((mmW s).length - mmM s ^ 2 + mmM s - 1) / mmM s
def mmA (s : List Bool) (i k : Nat) : Bool := ((mmW s).drop (mmM s ^ 2)).getD (i * mmM s + k) false
/-- C = A·B over GF(2), row-major. -/
def mmC (s : List Bool) : List Bool :=
  (List.range (mmRows s)).flatMap fun i => (List.range (mmM s)).map fun j =>
    (List.range (mmM s)).foldl (fun acc k => xor acc (mmA s i k && mmB s k j)) false
def checkMM (out s : List Bool) : Bool := padTo (mmC s).length out == mmC s
def correctMMB (J S : Nat) : Bool :=
  match runMul (str J) (str S) (clockMul (str J) (str S)) (str J).length with
  | some out => checkMM out (str S)
  | none => false
def CorrectMM (J S : Nat) : Prop := correctMMB J S = true
def SentenceMM : Prop := ∃ J, 1 ≤ J ∧ ∀ S, 1 ≤ S → CorrectMM J S
```

`runMul` and `clockMul` come from `ZP/DefsMul.lean`. Checks (`decide`): `mmC` and
`checkMM` on the examples of `zmm_ref.product` (for example `parse('110' + '1011' +
'0110' + '1')` gives `m = 2`, three rows of `A`), on `m = 0`, on `|w| ≤ m²` (empty
`C`), and the first beeps `('', '')`, `('0', '')`, `('1', '1011')`, `('00', '')`.

## 2. Generated files and base

```bash
python3 formal/gen_table.py zmm_native zmmMachine && python3 formal/gen_logic.py zmm
```

Add `'zmm': ('zmm', 'zmm_native', 'zmm', 'MM', None)` to `gen_logic.py`. zmm changes 2
zmul transitions (`GC,B` now goes to `X0`; `ER1,M` keeps `M`), removes zmul's
check (`TS TS2 RW HPF HPD SW CA* DR DE DU mP* mY* mX* mZ* FR0 FR1 FE`) and adds 70
states (none reuses a zmul name; `build()` asserts this).

**Sharing Z_MUL's proof.** `MulRun`, `MulSwitch`, `PairMul` (up to the check) are
stated for `zmulLogic.Reach`. Define `zmCore` = `zmulLogic` minus the transitions
listed above and generate it with `gen_logic.py` (the `gen_base` pattern of
`LogicBaseMul.lean`). Then either

- restate the Z_MUL lemmas that do not touch the check over `zmCore` (a search and
  replace of `zmulLogic.Reach` by `zmCore.Reach` in copies, plus `Ext` lifts at the two
  use sites), or
- better, state them once for any `L` with `Ext zmCore L`.

Prove `zmCore_ext_zmulLogic` and `zmCore_ext_zmmLogic` by `decide +kernel` in
`ZP/ExtChecks.lean`. The halt exit of `PairMul` (`hd FBACK … ⟶ hdR mK1 [2] …`, see plan
07's status notes) changes only in that `H` stays `M`: redo that one segment and
`mkChain`/`gcBodyC` (they are generated; rerun the generator on `zmmLogic`).

## 3. The check (`ZP/MMCheck.lean`, `ZP/MMRow.lean`)

Logical direction F = physical left. Print tapes on the Python machine at `X3`, `J1`,
`Z0`, `RS2`, `FA`, `D3`, `Q2`, `N2`, `RB2`, `E1` for the instances of
`tests/test_native.py::test_matmul_instances` before writing statements
(`formal/scripts/symexec.py` with `LOGIC=LogicMM LOGICID=zmm`; the docstring of
`native/zmm.py` explains each phase).

Layout during the check, read from `M_g` (see `docs/native.md`):

    M_g  B^c out'  Ms  acc[0..j) H acc[j+1..m)  Mr  B'  M  [A: M^q A']  s-end

where `out'` is the unconsumed part of `out` (the consumed `c` cells are blank), the
accumulator occupies the `m` ruler cells with one hole `H` (the cell after `H` is
column `j`; `H` sits just before `Mr` between B rows), `Mr` is `M` (`a = 0`) or blank
(`a = 1`), `B'` is `B` with one blank `P` (cells before `P` are shifted one cell
towards `M_g`), and `q` cells of `A` are consumed. In the dry row there is no `M`
between `B'` and `A`, and the accumulator holds the ruler (`1`s not yet marked, `0`s
marked).

1. **Setup** (`X0`–`X3`, `X3a`, `SM*`, then `RB*` from the end): from `GC`'s exit to
   `RS1` (which rewinds `H` from the ruler's end to its front) with `H` in place of the `0`,
   `Mr = M`, `P` in front of `B`. Loops: the skip loops `X0`–`X3`, the one-cell shift
   `SM0/SM1` over `w` (one lemma), the reverse shift `RB*` (one lemma over a bit
   string, reused in 6.).
2. **j-step** (`J1 S* T* W* U* Y*c Y2 Z0 Z1 G2`): one lemma. Pre: `P` before `v`,
   `H` before `acc[j]`. Post: `P` after `v`, `acc[j] := acc[j] xor (a && v)`, `H` after
   it. `Z0` then sees either another accumulator cell (`Z1 → G2 → J1`) or `Mr` (B row
   done, `Mr := M`, `RS1`). All loops are skip loops of the `MulCheck` shape.
3. **B row** (`m` j-steps): induction on `j`. Result: `acc := acc xor a · B_k`.
4. **Rewind and next a** (`RS1 RS2 RS3* G1 GA FA FB FC FD* FE*`): `RS*` moves `H` back to
   the front (`m` swaps, one lemma); then `FA` looks after `P`: a bit and then a `M`
   later (`FC`) fetches the front of `A` (or 0 past its end, `FC` on blank) into `Mr` and
   returns to `G2 → J1`; `FB` on blank (no boundary: dry row) goes to `D0`; `FA` on `M`
   (`P` at the boundary: row done) goes to `D0` too.
5. **Row** (induction on `k`): from the start of a row with `acc = out_i`, after `m` B
   rows `acc = out_i xor (row i of C)`.
6. **Row end** (`D0 D1 D3`, `Q2 Q4 Q5 Q6 Q7* Q8*`, `N1`–`N5`, `RB*`):
   - `D3` scans the accumulator: `0`s are skipped; a `1` is marked `0` and sent to `Z1`.
     In the dry row this is the B-row counter (next B row with `a = 0`, `Mr` still `M`).
     After a real row the next `J1` reads the boundary `M`: `VFa`, outcome 0.
   - all `0`: `Q2` loads the next `m` cells of `out` into the accumulator, one cell per
     round trip (`Q6` reads a bit and blanks it; `Ms` reached: 0).
   - `N1`–`N5`: `A` used up (blank after `P` or after the `M`s): `VC1`, outcome 1; else
     `RB*` shifts `B` back into `P` (dry row: `N4` shifts all of `w` from its end,
     `RBM` inserting the boundary `M` at `P`).
7. **Short `w`**: `J1` or `FA` reading `s-end` (blank) means `|w| ≤ m²`; outcome 1.
8. **Verdict** (`VC1 VC2 VC3`, `VFa VFb VF0`, `E1–E4`, `VW1–VW3`): to `Ms`, `Ms := o`,
   erase the four stretches (`acc`, up to `Mr`, `B'`, the rest of `w`), then blanks of
   the consumed `out` to 0 (`VW*`), then `ER1`. One lemma per entry point (`VC1`,
   `VC3` from setup with `m = 0` or `w = []`, `VFa`).
9. **Check theorem**:

```lean
theorem mmPhase (out s : List Bool) … :
    zmmLogic.Reach (hdR QMM.X0 …) (… ER1 with outcome (checkMM out s) …)
```

The bridge to `checkMM`: the rows are checked in order, so the run reaches `VFa` iff
some row `i < r` differs from `padTo` of `out`'s slice `[i m, (i+1) m)`, and `VC*`
otherwise. Prove `checkMM out s = true ↔ ∀ i < mmRows s, row i matches` in the
`DefsMM`-adjacent (untrusted) file `ZP/MMSpec.lean`.

## 4. Pair lemma and top

`pair_mainMM`: Z_MUL's `pair_mainMul` with `mmPhase` in place of `mulPhase` and
`frPath*`. Then `PairData zmmLogic CorrectMM` and

```lean
theorem zmmQuasihalts_iff_sentence : Quasihalts zmmMachine ↔ SentenceMM
```

Add to `Challenge.lean`, `Solution.lean`, `comparator.json` (`ZP.DefsMM`,
`ZP.TableMM`).

"`SentenceMM` ↔ multitape TMs compute the GF(2) matrix product in linear time" stays
on paper (`docs/native.md`), like plan 07's.

## Estimate

~3000–4500 lines, 3 sessions: (1) defs, checks, generated files, `zmCore` and the
retargeting of the Z_MUL lemmas; (2) setup, j-step, B row, next B row; (3) row end,
verdict, `mmPhase`, pair lemma, top.

## Checklist

- [x] `DefsMM` + checks; generated files, certificate (ZP/DefsMM.lean, ZP/ExtChecksMM.lean)
- [x] Ext facts (`zmBase_ext_zmmLogic`; no zmCore needed), Z_MUL lemmas retargeted (MMHalt, MMSwitch, MMRun, MMPair)
- [ ] setup, j-step, B row, next B row
- [ ] row end (dry, compare, fetch), reverse shift, verdict
- [ ] `mmPhase`, `pair_mainMM`, `zmmQuasihalts_iff_sentence`, Challenge/Solution

### Status (end of session 2)

Remaining: segment families via symbolic executor (setup SM/RB loops, j-step with
jc a v x := if a = 0 and v = 3 then 5 - x else x, B row induction, RS rewind, toFA,
fetch, dry row/D3, Q pass, N1-N5 shift, verdict stages 1 and 2), row loop, bridge
checkMM <-> row-wise in ZP/MMSpec.lean, mmPhase, haltPhaseMM, pair_mainMM, Main,
Challenge/Solution/comparator.
