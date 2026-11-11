# 12 — Z_PPOLY (`native/zppoly.py`, 325 states): `Quasihalts zppolyMachine ↔ SentencePoly`

Prerequisites: plan 01 (generic pipeline) and the zp2 development. The verifier phase
is zp2's unchanged; the new parts are the **outer loop** (a four-level enumeration) and
the **charge** of the advice length against the fuel.

Reference: `ref/zppoly_ref.py`; design: `docs/native.md` § "NP ⊆ P/poly"; machine:
`native/zppoly.py` (145 logical states).

## 1. Trusted definitions (`ZP/DefsPoly.lean`, mirrors `ref/zppoly_ref.py`)

```lean
def budget (K : List Bool) (n : Nat) : Nat := (n + 2) ^ (K.length + 1) - 1
/-- charged run: |a| steps up front. -/
def prun (a s : List Bool) (t : Nat) : Bool := if a.length ≤ t then run a s (t - a.length) else false
def advOK (K a : List Bool) (n : Nat) : Prop :=        -- a decides L on all of {0,1}^n
  ∀ s ∈ strings n, prun a s (budget K n) = inL s
def goodLen (K : List Bool) (n : Nat) : Prop := ∃ a, a.length ≤ budget K n ∧ advOK K a n
def SentencePoly : Prop := ∃ K : List Bool, ∀ n, goodLen K n
```

`inL` and `run` are zp2's (`ZP/Defs.lean`). `goodLen` is decidable: `a` ranges over the
finite set of strings of length `≤ budget K n`. Give the instance through a bounded
search in shortlex order that mirrors `events`, and prove it equivalent to the `∃`
(the machine finds the shortlex-first good `a`; any good `a` works for the sentence).

Checks (`ZP/ChecksPoly.lean`, `decide`): `budget`, `prun`, and the first events of
`zppoly_ref.events()`: `ok('', 0, '')`, `beep('', 1)`, `ok('0', 0, '')`,
`ok('0', 1, '0001')`. The next ones (`ok('0', 2, '00110001011')`) are too slow for
`decide`; leave them to the Python tests.

## 2. A new abstract program (`ZP/AbstractPoly.lean`)

The zp2 pipeline enumerates pairs `(J, S)`. Here the state is `(K, n, a, s)` with `s`
a counter of fixed length `n`:

| from | condition | to | beep |
|---|---|---|---|
| `(K, n, a, s)` | `budget K n < a.length` | `(K+1, 0, '', '')` | **yes** |
| `(K, n, a, s)` | `prun a s (budget K n) = inL s`, `s` not all 1s | `(K, n, a, s+1)` | no |
| `(K, n, a, 1^n)` | correct | `(K, n+1, '', 0^(n+1))` | no |
| `(K, n, a, s)` | wrong | `(K, n, a+1, 0^n)` | no |

Here `K+1` and `a+1` are shortlex successors and `s+1` is the binary successor. Prove

```lean
theorem abstractPoly_quasihalts_iff : AbstractQuasihaltsPoly ↔ SentencePoly
```

directly. (⇐) From some `K` on, no beep: for each `n`, the shortlex-first good `a` is
reached after finitely many wrong `a` (each of which is refuted by a wrong `s`), and is
never exhausted. (⇒) If every `K` fails at some `n`, every `K` is left with a beep:
every `a` of length `≤ budget` gets a wrong `s`, so `a` runs past the budget. The
measure for "K is left after finitely many steps" is `(n, rank a, s)` lexicographic,
bounded by the first bad `n`.

On the tape `K` is stored reversed; the layout function writes `K.reverse` and the
`K + 1` segment proves `rev (succ K) = incL (rev K)` for the left-to-right increment.

Then generalize `LMacroSimC` (`ZP/LogicalG.lean`) to an abstract step on `(K, n, a, s)`,
or encode the state as a pair `(K, code (n, a, s))` and reuse it with a custom step;
pick whichever needs fewer changes to `lmacroSim_of_pairs`. Write a design note first.

## 3. Generated files and base

```bash
python3 formal/gen_table.py zppoly_native zppolyMachine && python3 formal/gen_logic.py zppoly
```

zppoly overrides zp2 inside `native/zppoly.py` (zp2 itself is unchanged):

- **12 changed zp2 transitions**: `BN3,M`, `DG3,M`, `VG3,M`, `DP10,M`, `DP11,M` (one
  more field to skip), `CX,1`, `CX,M`, `CX,B` (BLK dispatch), `WB2,B` (charge),
  `EBj,M` (wrong answer), `SOV,B` (correct answer, overflow), `JOV2,B` (start and
  `K + 1`).
- **8 new transitions on zp2 states**, all on keys that zp2 leaves undefined, so they act
  as fresh exits: `GC,B`, `PK1,M`, `EL2,M` (charge), `SOV,M`, `FB,0` (`a + 1` carry),
  `JOV2,0`, `JOV2,1`, `JOV2,M` (`JOV2` writes `M` on any cell).
- **Deleted zp2 states**: `BD1`–`BD6` (zp2's BLK dispatch by counting fields), `JE3`,
  `JINC`, `JOV` (zp2's `J + 1`).
- **25 new states**: `BNA`, `DGA`, `VGA`, `DPX0`, `DPX1` (field skips); `CXC`, `CXV`,
  `CXD` (dispatch); `CHS`, `CK`, `CK2`, `CK3`, `CD`, `U`, `V` (charge); `Z3`, `BEEPX`,
  `KINC`, `J2` (beep, `K + 1`); `ZS`, `AOV3` (wrong); `DL5`, `DL1`, `DL3`, `DL4`
  (correct).

The beep state is `BEEPX`. zp2's `BEEP` keeps its transition (`BEEP,M → 0,R,EAs`) but
is not the beep state: it only marks a wrong answer (the flag cell becomes `0`, so
`EBs` goes to `EBj`). Define `zpolyBase` = `zpBase` minus the changed and deleted
transitions (plan 07 pattern) and retarget the surviving zp2 lemmas. A zp2 lemma whose
run never reads one of the 8 new keys holds unchanged; the ones whose run ends on such
a key (the copy loop at `GC`, the fuel loop at `PK1`, the exhaustion at `EL2`, the
counter at `SOV`) get a new exit case instead of the zp2 one.

## 4. Layout and phases

Between runs: `M_g rev(K) M_1 a M_a s M_2 C M_3 fuel` (verifier phase),
`M_g rev(K) M_1 a M_a s M_2 M [1] M_3 fuel` (decider phase). **`K` is stored last bit
first** (`rev K` on the tape), so that the shortlex `K + 1` runs left to right from
`M_g`; the walker only uses `|K|`. The extra field `a` sits between `M_1` and `s`: every
navigation that zp2 does by counting fields gets one more field (`BNA`, `DGA`, `VGA`,
`DPX*`). Restate zp2's layout functions with the field and check, segment by segment,
that only the counts change.

Print tapes on the Python machine at `GRB`, `WB2`, `CHS`, `CD`, `U`, `PK1`, `EL2`,
`BEEPX`, `J2`, `ZS`, `SINC`, `SOV`, `FB`, `AOV3`, `DL*` for `K = ''` and `K = '0'`
before writing statements (run the logical machine and print `logic.show(tape, h)` on
entry to those states).

| phase | reuse | new |
|---|---|---|
| verifier (truth of `s ∈ L`) | zp2's verifier loop, with the extra field | field-skip segments |
| BLK dispatch | zp2's copy loop up to its exit `CX` | `CX` reads the cell after `M_2`. `1 → CXC`: the field `C`; `CXC,B` and `CX,B` (`C` with `n = 0`) write the last `1` and `FB` writes `M_3`; `CXC,M → CXV`: verifier fuel built `→ VG1`. `M → CXD`: decider fuel block built `→ DW1` |
| decider fuel | zp2's walker, with `K` for `J` | `WB2,B → CHS` (`H` written) |
| **charge** | zp2's guest copy `GC` (exit `GC,B`), zp2's odometer `FR … DEC1 … FBACK → PK1` (exit `PK1,M`) | `CHS → CK → CK2` blanks `M_a`, `CK3 → GC` copies `a` as tokens left of `H`; `GC,B` restores `M_a`, `CD` goes to the first token, `U` turns it into the marker `M_t`, `V` turns `H` into the gap and enters `FR`. After each decrement `PK1,M` blanks `M_t`, `U` puts it on the next token. No token left: `U,B` writes `H`, `U,M` (`a = ''`) keeps it; both go to `DG2` |
| decider run | zp2's `runFrom` with code `a`, source `s`, fuel = clock − `\|a\|` | — |
| beep | zp2's exhaustion `DEC1,M → EXH → GHH0 → EL1 → EL2` (`GHH0` turns `M_g` into `0`) | `EL2,M` (meets `M_t`) `→ Z3` restores `M_g` `→ BEEPX` |
| `K + 1`, reset | zp2's eraser `VA3 → VA4 → FB → GRB` | `BEEPX`/`KINC`: `1 → 0` carry, `0 → 1 → J2` skips to `M_1`; carry out at `M_1`: `0`, then `JOV2` writes `M_1` one cell right. Then `VA3` erases right of `M_1`, `FB` writes `M_a`, `GRB` writes `M_2` |
| wrong | zp2's `DP40/DP41 → BEEP → EAs … EBs → EBj`, zp2's `SINC` on `a` | `EBj,M → ZS`: `s := 0^n`, then `SINC` on `a`. Carry out of `a`: `SOV` meets `M_a`, `SOV,M` writes `0`, `FB,0` writes `M_a` over the first cell of `s`, `AOV3` appends a `0` |
| correct | zp2 `EBs → SINC` (binary on `s`) | carry out of `s`: `SOV,B` appends a `0` `→ DL5 → DL1 … DL4`: delete `a` cell by cell (shift `M_a` and `s` left), `DL1,M → GRB` |

`SINC` is the same increment for `s` and for `a` (from the right end, a carry moves
left, `SINC,M → SOV`); `SOV` then runs right over the zeros and tells the two cases
apart by what it meets: a blank after `s` (correct, `n + 1`) or `M_a` after `a`
(wrong, `|a| + 1`).

**The charge lemma.** Charging `|a|` units against a fresh odometer of value
`budget K n` (zp2's `fuelVal` at the walker's end) either leaves value
`budget K n − |a|` (then the decider run is zp2's run with clock `budget − |a|`) or
exhausts it exactly when `|a| > budget K n`. One induction over the remaining tokens,
with invariant `B… B M_t t_(i+1) … t_k gap M_g …` (blanks left of `M_t`, the tokens
contiguous up to the gap), using the decrement lemma of `ZP/Fuel.lean` per token
(`FR → … → FBACK → PK1`, then `PK1` skips the tokens to `M_t`). On exhaustion, `EL2`
erases the tokens leftwards and meets `M_t` before any blank; in a guest run's
exhaustion `EL2` must meet `B` (zp2's exit `EL3`) and never an `M`: prove that the
cells left of the guest tape are blank there. After a completed charge all cells left
of `H` are blank, which is what zp2's decider-run setup expects.

## 5. Top

```lean
theorem zppoly_quasihalts_iff_sentence : Quasihalts zppolyMachine ↔ SentencePoly
```

Add to `Challenge.lean`, `Solution.lean`, `comparator.json` (`ZP.DefsPoly`, `ZP.TablePoly`).

"`SentencePoly` ↔ NP ⊆ P/poly" stays on paper: `SentencePoly` says `L` has advice
programs of size and time `(n+2)^(c+1)`; `L` is NP-complete (proved for zp2:
`ZP.Cx.sentence_iff_PeqNP`'s hardness half), and P/poly is closed under polynomial-time
reductions. A Lean version needs a definition of P/poly; write a design note first.

## Estimate

~4000–5500 lines, 3–4 sessions: (1) defs, checks, the abstract program and its
quasihalting theorem; (2) base, layout with the extra field and reversed `K`, field-skip
segments, BLK dispatch, verifier phase; (3) charge lemma (token marker over zp2's
odometer), decider phase; (4) beep/wrong/correct successors, the
macro simulation on the new state space, top theorem.

## Checklist

- [ ] `DefsPoly` + `ChecksPoly`
- [ ] `AbstractPoly`: four-level enumeration, `abstractPoly_quasihalts_iff`
- [ ] generated files, certificate, `zpolyBase`
- [ ] layout with `a` and reversed `K`, BLK dispatch, verifier phase, decider fuel
- [ ] charge lemma, decider run
- [ ] beep / wrong / correct successors, macro simulation, `zppoly_quasihalts_iff_sentence`
