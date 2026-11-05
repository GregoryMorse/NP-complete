# 04 — Z_DLOG (`native/zdl.py`, 400 states): `Quasihalts zdlMachine ↔ SentenceD`

Prerequisite: plan 03 (the glue `GlueF` and the conversion `ConvF`).

**Shape.** This is zfac with the divisibility loop (`DIV` states) replaced and the
conversion's end transitions `(HPF,M)`, `(HPD,M)` re-pointed. The rest is the same:
new-instance glue, copy, Horner conversion, result path and decider. So the
conversion lemma of plan 03 must have its **end** segment split off. That is, prove
`conv` up to "copy used up, state HPF/HPD on M", and let each machine supply the
last step.

## 1. Trusted definitions (`ZP/DefsD.lean`, mirrors `ref/zdl_ref.py`)

```lean
def isPrime (p : Nat) : Bool := decide (2 ≤ p) && (List.range p).all fun d => decide (d < 2) || p % d != 0
def dlogLoop : Nat → Nat → Nat → Nat → Nat → Bool     -- fuel k+1, y, g, h, p: the ref's for-loop
  | 0, _, _, _, _ => false
  | f + 1, y, g, h, p => if y = h then true else dlogLoop f (y * g % p) g h p
def inLD (s : List Bool) : Bool :=
  match (numbers s).reverse with
  | p :: g :: h :: r => isPrime p && dlogLoop (r.headD 0 + 1) 1 g h p
  | _ => false
def SentenceD : Prop := SentenceC (CorrectF inLD)
```

Here `k = r.headD 0` (0 when there are only three numbers). Mirror the ref's loop **exactly**:
- `y = 1` initially;
- `k + 1` iterations;
- the check happens before the multiply.

Note that `y = 1` is compared with `h` before any reduction mod p. With `p ≥ 2`
that is fine, but keep it literal. Add `decide` checks against `zdl_ref.in_LD` on
~30 strings, and the first beeps.

## 2. Generated files

Run:
- `gen_table.py zdlog_native zdlMachine`, giving `ZP/TableD.lean`;
- `gen_logic.py zdl`, with parent zfac, giving `ZP/LogicD.lean`.

Prove `zfConv.Ext zdlLogic` (glue + conversion are shared; this was measured: 68 of
zfac's 106 own transitions are identical in zdl).

## 3. New phases (Python trace first)

Start layout after the conversion: `B .. P M G M H M K M (gap) M_g`.

1. **Primality** (≈ divisibility with roles swapped).
   - `D := copy of P` at the left edge.
   - For `d = p−1 … 2`: `D` shrinks by one at its left edge, then `d | p` is tested by
     marking cells of `P` and `D` in turn, with an eager reset of `D`.
   - Outcomes:
     - `p` is used up exactly when `D` is all 1s, which means divisible: reject
       (`FR0`);
     - `D` is down to one cell: prime, and that cell becomes `Y = 1`.
   - Lemma shape: copy the plan-03 `divTest` and outer induction, with the `i % d`
     invariant. Prove `p < 2 →` reject, matching `isPrime`.
   - Bridge `∀ d, 2 ≤ d < p → p % d ≠ 0` to `isPrime` (a `List.all` over `range`
     lemma).
2. **Compare** `Y` with `H` by marking both (equal lengths ⇔ accept, `FR1`), restoring
   the marks.
3. **Count.** Mark one cell of `K`. If none is left, reject. The loop runs `k + 1`
   compares, so check the off-by-one against `dlogLoop (k+1)` on the Python machine.
4. **Multiply mod p.** For every cell of `G`, for every cell of `Y`, mark the next cell
   of `P`, resetting `P` when full. Then rebuild `Y` at the left edge from `P`'s marked
   cells, so `Y := (Y·G) mod P`.
   - Invariant: after `i` cells of `G` and `j` cells of `Y`, `(i·y + j) mod p` cells of
     `P` are marked.
   - Two nested inductions with `Nat.mod` arithmetic: `Nat.add_mod`,
     `Nat.mul_succ`, and generalize before `omega`.
   - Edge cases: `g = 0` or `y = 0` gives `Y := 0`. Check what the machine does with an
     empty `Y` block in the compare.
5. **Loop.** Induction on the remaining `K` cells. Each round is compare, then count,
   then multiply. Conclude
   `o = dlogLoop (k+1) 1 g h p` (given prime `p`).
6. **Result, decider, successors, top theorem**: as plan 03, step 4–6.
   ```lean
   theorem zdl_quasihalts_iff_sentence : Quasihalts zdlMachine ↔ SentenceD
   theorem zdl_quasihalts_iff_InP : Quasihalts zdlMachine ↔ InP (fun s => inLD s = true)
   ```

## Note on the statement

`L_D` includes "p is prime", so the function version ("discrete log mod primes in
P") would need primality in P (AKS). That is out of scope, and **the formal target is
`L_D ∈ P`**; say so in the docstring.

## Files

`DefsD`, `ChecksD`, `TableD`, `LogicD` (generated), `CompileD`, `PrimeD`, `ModMulD`,
`PairD`.

## Estimate

~2500–3500 lines. The multiply-mod-p double loop is the main risk; design its invariant
on the Python trace before writing Lean.

## Status: DONE

`ZP/PairD.lean` (~2000 lines): primality (`cpLoop pLoop scanXS primePhase`), comparison (`cmpLoop`),
discrete-log loop (`dlogStep dlogMain`), multiplication mod p (`iLoop oLoop tLoop mulPhase`),
layout cases for 1, 2, 3, ≥4 numbers (`truthD`), `newInstD`, `pair_mainD`; `MainD`.
Recipe unchanged from plan 03 (generate segments with `symexec.py`, then `rep`-induction loops).
