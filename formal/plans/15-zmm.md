# 15 — Z_MATMUL (`native/zmm.py`, 577 states): `Quasihalts zmmMachine ↔ SentenceMM`

Prerequisites: plan 07 (Z_MUL, done). This machine **is** Z_MUL with a new output
check: the guest model, fuel, switch, run theorem, setup and dispatch are Z_MUL's.
Only the check after a proper halt changes. So the work is (a) making the Z_MUL
lemmas usable from a second machine and (b) one new check routine.

Reference: `ref/zmm_ref.py`; design: `docs/native.md` § "Linear-time GF(2) matrix
product"; machine: `native/zmm.py` (248 logical states: zmul minus its check, plus 105
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
check (`TS TS2 RW HPF HPD SW CA* DR DE DU mP* mY* mX* mZ* FR0 FE`; `FR1` is reused
as a name for a new state) and adds 105 states.

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

Logical direction = physical left. Print tapes on the Python machine at `X3`, `J1`,
`TR4`, `RE3`, `CM`, `NF4`, `VF0`, `VF1`, `E4` for the instances of
`tests/test_native.py::test_matmul_instances` before writing statements
(`formal/scripts/symexec.py` with `LOGIC=LogicMM LOGICID=zmm`).

Layout during the check, read from `M_g` (see `docs/native.md`):

    M_g  0^c out'  Ms  1^(m-k) 0^k  Mr  B'  [A: M^q A']  s-end  M^e a M^u acc_old  sep  acc_new  end

where `out'` is the unconsumed part of `out` (the consumed `c` cells are blank),
`B'` is `B` with one blank `P` (the cells before `P` are shifted back by one), `q`
cells of `A` are consumed, and `k` ruler cells are marked.

1. **Setup** (`X0`–`X3`, `SH*`, `AI*`, `AB*`, `AF*`, `RR*`): from `GC`'s exit to `J1`
   with `P` in front of `B`, `a = 0`, `acc_old = 0^m`, `acc_new` empty. Three loops: the
   ruler skip in `X3`, the shift chain `SH*` (one lemma over `w`), the ruler copy
   `AB3 … AF4` (`m` iterations).
2. **j-step** (`J0 J1 JF* JA* JC* JW* JX* JB* SL*`): one lemma. Pre: the layout with
   `P` before cell `v`, `acc_old = o :: rest`. Post: `P` after `v`, `acc_old = rest`,
   `acc_new ++ [o xor (a && v)]`. Each `JF/JA/…` is a skip loop of the shape already
   proved in `MulCheck` (`dloopM`-style); reuse the skip lemmas.
3. **B row** (`m` j-steps, then `acc_old` empty): induction on `j`. Result:
   `acc_new = zipWith (xor) acc_old (a · B_k)`.
4. **Next B row** (`TR1`–`TR5`, `FA*`, `FC*`, `FE*`, `FG*`, `FR*`): mark the ruler; if a
   `1` is left, fetch `a'` (front of `A`, or `0` past its end, or `0` in the dry row:
   `FA4` meets `P` before any `M`), write it into `sep`, and return to `J1`. If not,
   `RE1`.
5. **Row** (induction on `k`): from the start of a row, `acc_new` at the row end is
   `acc_init xor Σ_k a_k · B_k`. With `acc_init = 0^m` this is row `i` of `C`.
6. **Row end** (`RE*`, `DC*`, `SE*`, `SG*`, `ZR`, `ZB*`, `RS*`, `CM`, `CB*`, `CF*`,
   `NF*`):
   - dry row (`RE3` reads a bit): it becomes the first `a`, the accumulator is zeroed,
     `B` is shifted back;
   - other rows: `acc_new` is compared with the next `m` cells of `out` (padded); a
     mismatch goes to `VF0`; then `NF4` fetches the next row's first `a` (none: `VB`,
     outcome 1), zeroes the accumulator, shifts `B` back.
   The reverse shift `RS*` is the inverse of the slides of 2.–3. (one lemma over
   `B`).
7. **Dry row and empty `A`**: `J1` reading `s-end` means `|w| ≤ m²`; outcome 1.
8. **Verdict** (`VB VC VD VF* FB* E1–E4`): to `Ms`, blanks of the consumed `out` to 0,
   `Ms := o`, erase the four stretches, then `ER1`. One lemma per entry point (three:
   `VB`, `VF0` from the out region, `VF1` from `Ms`).
9. **Check theorem**:

```lean
theorem mmPhase (out s : List Bool) … :
    zmmLogic.Reach (hdR QMM.X0 …) (… ER1 with outcome (checkMM out s) …)
```

The bridge to `checkMM`: the rows are compared in order, so the run reaches
`VF0` iff some row `i < r` differs from `padTo` of `out`'s slice `[i m, (i+1) m)`, and
`VB` otherwise. Prove `checkMM out s = true ↔ ∀ i < mmRows s, row i matches` in
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

- [ ] `DefsMM` + checks; generated files, certificate
- [ ] `zmCore`, Ext facts, Z_MUL lemmas over `zmCore`
- [ ] setup, j-step, B row, next B row
- [ ] row end (dry, compare, fetch), reverse shift, verdict
- [ ] `mmPhase`, `pair_mainMM`, `zmmQuasihalts_iff_sentence`, Challenge/Solution
