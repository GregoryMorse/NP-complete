# 06 — Z_PSPACE (`native/zps.py`, 291 states): `Quasihalts zpsMachine ↔ SentencePS`

Prerequisites: plans 01 and 02 (it reuses `ZP/Count.lean`'s `bv`/`ofBv` only lightly).
It is the smallest diff from zp2:
- 4 zp2 states change (`DP30`, `DP31`, `VN1`, `VN2`);
- the `WK{r}{E|A}` walker states are added.

The proof idea is a clean recursion, so this plan is mostly one induction.

## 1. Trusted definitions (`ZP/DefsPS.lean`, mirrors `ref/zps_ref.py`)

```lean
/-- Value of the game node with certificate prefix `p` and `d` levels below it
(`ref/zps_ref.val`; at depth `d + 1` the player is ∃ iff `d` is even). -/
def gval (s : List Bool) : Nat → List Bool → Bool
  | 0, p => run s p (s.length + 1)
  | d + 1, p =>
    let ex := d % 2 == 0
    let a := gval s d (p ++ [true])
    if a == ex then a else gval s d (p ++ [false])
def inLPS (s : List Bool) : Bool := gval s (s.length + 1) []
def SentencePS : Prop := SentenceC (CorrectF inLPS)
```

**Check the parity.** In the ref, `i = len(prefix)` and `exists = (n - i) % 2 == 0`. At
depth `d + 1` we have `i = n − d`, so `exists ↔ d % 2 = 0`. Also add `decide` checks of
`inLPS` against `zps_ref.in_LPS` on the first ~25 strings, plus the first beeps.

## 2. Generated files

Run:
- `gen_table.py zps_native zpsMachine`;
- `gen_logic.py zps`;
- prove `zpBase.Ext zpsLogic`.

## 3. Layout and the walker

The certificate counter `C` sits on the tape left to right as `c_0 … c_n`, the
certificate passed to `run`. (zp2's `GCv` writes `bitsOf cl.reverse` and runs
`run Sb cl.reverse`; confirm the same on the Python machine.) The initial value is all
1s ("first child = 1"), built exactly as in zp2, so `vStart` is reused.

After a verifier run with result `r`, the walker starts **at C's last bit**, with
parity `E`, and moves left with alternating parity:

| at | condition | action |
|---|---|---|
| bit `0` | second child done | write `1`, go left (flip parity) |
| bit `1` | `r` dominant (`1` for E, `0` for A) | go left (flip parity), bit stays `1` |
| bit `1` | `r` not dominant | write `0`, go right to `VFE` (refill: the rest of C is all 1s), then run the next verifier |
| `M_2` | root reached | truth `r`: `VA1` for 1, `VU2` for 0 |

## 4. The key lemma (`ZP/GamePS.lean`)

**Invariant:** when a node returns, every bit of its subtree is `1` again.
- A short-circuit leaves the bit at `1`.
- A finished second child resets its bit to `1`.
- `VFE` relies on the rest being 1s.

```lean
/-- Running the subtree at prefix `p` (with `d` levels below) from the verifier start
returns its value to the walker at `p`'s last bit, with C restored. -/
theorem node (j) (hj : Bits j) (Sb : List Bool) :
    ∀ d p, p.length + d = Sb.length + 1 →
      zpsLogic.Reach (runStartPS j Sb (p ++ List.replicate d true))
        (walkAt j Sb (p ++ List.replicate d true) p.length (gval Sb d p))
```

Here `walkAt … i r` is the walker in state `WK{r}{parity}` on bit `i − 1` of C, or on
`M_2` when `i = 0`. The parity is a function of `Sb.length + 1 − i`, so compute it
once and prove the `E`/`A` alternation as a `% 2` lemma.

**Proof:** induction on `d`.
- `d = 0`: one verifier run. Reuse zp2's run segments (`setup`, `runFrom`, `gcLoop`,
  `qcLoop`, via `Ext`). Then the new `DP3o → DPVo → WK{o}E` segments, starting at the
  last bit.
- `d + 1`, with `p' = p ++ [true]`:
  - By IH on `p'` the walker arrives at bit `|p|` (the `true`) with `a = gval d p'`.
  - Case `a` dominant: one walker step left, and `gval (d+1) p = a`, done.
  - Case `a` not dominant:
    - Write `0` and refill (`VFE`, a segment over a block of 1s plus the fuel block).
      That reaches `runStartPS … (p ++ false :: replicate d true)`.
    - By IH on `p ++ [false]`, the walker arrives back at the `false` bit with
      `b = gval d (p ++ [false])`.
    - The bit-`0` walker step writes `1` and moves left, so C is restored and
      `gval (d+1) p = b`.
  - The value bookkeeping is `simp [gval]` plus `cases a <;> cases (d % 2 == 0)`.

**Root:** `node (Sb.length + 1) []` gives the walker at `M_2` with `inLPS Sb`. Then the
truth segments `VA1`/`VU2` lead to zp2's `TR j Sb (inLPS Sb)`, and from there the zp2
decider/compare/successor lemmas apply through `Ext`.

## 5. Top

`pairPS_main`, then `lmacroSim_of_pairs zpsLogic (CorrectF inLPS) lay 2 …`. Then:

```lean
theorem zps_quasihalts_iff_sentence : Quasihalts zpsMachine ↔ SentencePS
theorem zps_quasihalts_iff_InP : Quasihalts zpsMachine ↔ InP (fun s => inLPS s = true)
```

Add the first theorem to Challenge/Solution/comparator.

## Optional, later

`SentencePS ↔ P = PSPACE` needs a PSPACE definition and a hardness proof (a QBF
reduction with the padding of `Hard.lean`). Write a design note before any Lean.

## Estimate

~1200–2000 lines, the smallest after PP. The walker segments are 4 states × 2 values,
generated with symexec.

## Status: DONE

Files: `ZP/DefsPS`, `ChecksPS`, `TablePS`, `LogicPS`, `CompilePS`, `PairPS`, `MainPS`.
Same recipe as plan 02. Notes:
- Only the four dispatch lemmas (`vAcc vRejE vRejC vUnder`) fail when `Pair.lean` is copied for `zpsLogic`.
- The generated walker lemmas (`toWK1_*, toWK2_*, wk0_*, wk1d_*, wk1n_*, wkM_*, refill, root*`)
  are single steps or small sweeps; wrappers `wk0_gen/wk1d_gen/wk1n_gen/wkM_*` hide the
  parity bookkeeping (`wkQ r d`).
- `nodePS` is the game-tree induction; `vFullPS` handles the root; `pair_mainPS` is the copy of
  `pair_main`.
