# 12 — Z_PPOLY (`native/zppoly.py`, 371 states): `Quasihalts zppolyMachine ↔ SentencePoly`

Prerequisites: plan 01 (generic pipeline) and the zp2 development. The verifier phase
is zp2's unchanged; the new parts are the **outer loop** (a four-level enumeration) and
the **charge** of the advice length against the fuel.

Reference: `ref/zppoly_ref.py`; design: `docs/native.md` § "NP ⊆ P/poly"; machine:
`native/zppoly.py` (166 logical states).

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

Then generalize `LMacroSimC` (`ZP/LogicalG.lean`) to an abstract step on `(K, n, a, s)`,
or encode the state as a pair `(K, code (n, a, s))` and reuse it with a custom step;
pick whichever needs fewer changes to `lmacroSim_of_pairs`. Write a design note first.

## 3. Generated files and base

```bash
python3 formal/gen_table.py zppoly_native zppolyMachine && python3 formal/gen_logic.py zppoly
```

zppoly changes 13 zp2 transitions (`BD3,M`, `BN3,M`, `DG3,M`, `DP10,M`, `DP11,M`,
`DP40,1`, `DP41,M`, `EBj,M`, `JINC,0`, `JOV2,B`, `SOV,B`, `VG3,M`, `WB2,B`), removes
`BEEP` and `JE3`, and adds 39 states. The beep state is `BEEPX`. Define `zpolyBase` =
`zpBase` minus the changed transitions (plan 07 pattern) and retarget the surviving
zp2 lemmas.

## 4. Layout and phases

Between runs: `M_g K M_1 a M_a s M_2 C M_3 fuel` (verifier phase),
`M_g K M_1 a M_a s M_2 M [1] M_3 fuel` (decider phase). The extra field `a` sits
between `M_1` and `s`: every navigation that zp2 does by counting fields gets one more
field (`BNA`, `BDA`, `DGA`, `VGA`, `DPX*`). Restate zp2's layout functions with the
field and check, segment by segment, that only the counts change.

Print tapes on the Python machine at `GRB`, `WB2`, `CHS`, `CA`, `XD1*`, `CDN`, `BEEPX`,
`WRG`, `ZS`, `AINC`, `AOV*`, `SOV`, `DL*` for `K = ''` and `K = '0'` before writing
statements.

| phase | reuse | new |
|---|---|---|
| verifier (truth of `s ∈ L`) | zp2's verifier loop, with the extra field | field-skip segments |
| decider fuel | zp2's walker, with `K` for `J` | `WB2,B → CHS` (no `H` yet) |
| **charge** | zp2's `DEC`/`RF`/`RG` odometer lemma (`ZP/Fuel.lean`) | loop `CA → XR b → XD1 b … → XK b → CA`: blank a cell of `a`, decrement the fuel once, restore the cell. Exhaustion `XD1 b, M → BEEPX` |
| decider run | zp2's `runFrom` with code `a`, source `s`, fuel = clock − `|a|` | `CDN` writes `H` |
| beep | — | `BEEPX → EXC → EXD → EXG → JINC → JX1 → JX2 → GRB` (erase right of `M_1`, `K + 1`) |
| wrong | — | `WRG → EAs …  EBj → ZS → AINC → (AOV …)`: `s := 0^n`, `a := a + 1` with the shift on a carry |
| correct | zp2 `SINC` (binary on `s`) | `SOV → DL5 → DL1 … DL4`: append a cell to `s`, delete `a` cell by cell |

**The charge lemma.** Charging `|a|` units against a fresh odometer of value
`budget K n` (zp2's `fuelVal` at the walker's end) either leaves value
`budget K n − |a|` (then the decider run is zp2's run with clock `budget − |a|`) or
exhausts it exactly when `|a| > budget K n`. One induction over the cells of `a`, using
the decrement lemma of `ZP/Fuel.lean` per cell.

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
quasihalting theorem; (2) base, layout with the extra field, field-skip segments,
verifier phase; (3) charge lemma, decider phase; (4) beep/wrong/correct successors, the
macro simulation on the new state space, top theorem.

## Checklist

- [ ] `DefsPoly` + `ChecksPoly`
- [ ] `AbstractPoly`: four-level enumeration, `abstractPoly_quasihalts_iff`
- [ ] generated files, certificate, `zpolyBase`
- [ ] layout with `a`, verifier phase, decider fuel
- [ ] charge lemma, decider run
- [ ] beep / wrong / correct successors, macro simulation, `zppoly_quasihalts_iff_sentence`
