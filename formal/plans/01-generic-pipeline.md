# 01 — Make the Z_P pipeline generic (prerequisite for every other plan)

Today every layer is welded to one machine: `Correct`/`inL` (Abstract, Bridge),
`zpLogic`/`Q.*` (Rot … Pair, Logical) and `zpMachine` plus the literal `129`
(Compile). The machines Z_PP, Z_PSPACE, Z_FACTOR, Z_DLOG and Z_GI are zp2 with
**59 of zp2's 366 logical transitions changed or removed** plus new states, so
most of the N3 proof can be reused if the layers take the machine as a parameter.
Do this refactor once, keep `zp_quasihalts_iff_sentence` green throughout, and
every later plan becomes "new Defs + new truth routine + glue".

Target size: ~600–900 changed/new lines. Do the steps in order and build after each.

## Step A — Abstract layer over any refutation predicate (`ZP/Abstract.lean`)

Generalize over `C : Nat → Nat → Prop` with `[∀ J S, Decidable (C J S)]`:

```lean
def absStepC (C : Nat → Nat → Prop) [∀ J S, Decidable (C J S)] (p : Nat × Nat) : Nat × Nat :=
  if C p.1 p.2 then (p.1, p.2 + 1) else (p.1 + 1, 1)
def absStateC (C) [..] : Nat → Nat × Nat      -- iterate from (1, 1)
def AbstractQuasihaltsC (C) [..] : Prop       -- same shape as today
def SentenceC (C) : Prop := ∃ J, 1 ≤ J ∧ ∀ S, 1 ≤ S → C J S
theorem abstractQuasihaltsC_iff (C) [..] : AbstractQuasihaltsC C ↔ SentenceC C
```

The existing proofs never use what `Correct` is, so the generalization is a search and
replace. Then redefine the old names as abbreviations
(`abbrev absStep := absStepC Correct`, …) so the rest of the tree still compiles.
Check that `abstractQuasihalts_iff_sentence` is now a one-liner.

(Z_NTT has a *different* abstract program, where a refutation keeps `S`. Do **not**
generalize for it now; plan 08 adds its own.)

## Step B — Bridge (`ZP/Bridge.lean`)

`MacroSim M` → `MacroSimC C M` (it mentions only `absState` and `Correct`).
`quasihalts_iff_of_macroSimC : MacroSimC C M → (Quasihalts M ↔ AbstractQuasihaltsC C)`.
Keep `MacroSim := MacroSimC Correct`.

## Step C — Compile generic in the machine and certificate (`ZP/Compile.lean`)

Today it uses `zpLogic`, `zpMachine`, `zpEntry`, `zpSide`, `zpGlen` and `129`.
Bundle these:

```lean
structure Cert where
  L : LTM            -- logical machine
  T : TM             -- table
  n : Nat            -- number of logical states (= L.table.length)
  entry : List Nat
  side  : List Nat
  glen  : List (List Nat)
```

and make the definitions/lemmas take `(K : Cert)`. The kernel checks (`hchk`,
`beep_entry`, `zpLogic_len`) become hypotheses bundled as
`structure Cert.OK (K : Cert) : Prop` with the three `decide`-able facts. End with:

```lean
theorem macroSimC_of_logic (K : Cert) (hK : K.OK) (S : LMacroSimC C K.L) : MacroSimC C K.T
```

Then re-derive `zp_macroSim` from `zpCert` and `zpCert_ok : zpCert.OK := ⟨by decide +kernel, …⟩`.
**Watch the kernel cost:** `hchk` is the expensive check. Keep it as one `decide +kernel`
per certificate, in the machine's own file, so it is evaluated once.

`LMacroSim` (`ZP/LTM.lean`) gets the same `C` parameter.

## Step D — Machine extension and run transfer (new `ZP/Ext.lean`)

```lean
/-- `M'` does everything `M` does (and maybe more), with the same beep state. -/
def LTM.Ext (M M' : LTM) : Prop :=
  M.beep = M'.beep ∧ ∀ q a r, M.act q a = some r → M'.act q a = some r
theorem LTM.Ext.zstep {M M'} (h : M.Ext M') {c c'} : M.zstep c = some c' → M'.zstep c = some c'
theorem LTM.Ext.zrun  {M M'} (h : M.Ext M') : ∀ n c c', M.zrun n c = some c' → M'.zrun n c = some c'
theorem LTM.Ext.reach {M M'} (h : M.Ext M') {c c'} : M.Reach c c' → M'.Reach c c'
theorem LTM.Ext.reach1 …        -- same for Reach1
```

`zrun` refuses to step from the beep state, which is why `Ext` requires the same beep
number. The proof is induction on `n` with `LTM.zstep` unfolded. Also provide a
decidable form for concrete machines:

```lean
def extB (M M' : LTM) : Bool   -- rows of M' agree with M wherever M's code ≠ 0, same beep
theorem ext_of_extB : extB M M' = true → M.Ext M'
```

so `Ext zpBase zppLogic` is `ext_of_extB (by decide +kernel)`.

## Step E — `zpBase` and numbering-compatible generated machines (`gen_logic.py`)

1. **`zpBase`** = `zpLogic` with these 59 transitions set to code 0. This is the union
   over zpp/zps/zfac/zdl/zgi of the zp2 transitions they change or delete; regenerate
   the list with the snippet below rather than trusting this file:
   - BD1–BD6 (all symbols)
   - VA2, VA3, VA4, VF2, VFE, VG1, VG2, VG3, VN1, VN2, VU2 (the defined symbols)
   - DP30/DP31 on `0`,`1`
   - (GC,M), (CX,B), (SINC,0), (JINC,0), (SOV,B), (JOV2,B)

   ```python
   import zp2, zpp, zps, zfac, zdl, zgi
   bd = zp2.build().d
   vol = set().union(*({k for k in bd if mod.build().d.get(k) != bd[k]}
                       for mod in (zpp, zps, zfac, zdl, zgi)))
   ```
   (Z_MUL changes 16 more, inside the interpreter's halt path. It gets its own base in
   plan 07, so leave it out here.)

2. **Generator.** Refactor `gen_logic.py` into `gen_logic.py <machine>` (default `zp2`,
   which must reproduce today's `ZP/Logic.lean` byte for byte, so CI stays happy). For
   machine X, emit `ZP/Logic<X>.lean` containing:
   - `xLogic`, `xCert`;
   - a `namespace QX` holding **only the new state names**.

   **Numbering rule:**
   - every state name that exists in zp2 keeps zp2's number;
   - zp2 states that X deletes keep their slot with an all-zero row;
   - X's new states are numbered from 129 upward, in `m.states()` order.

   Then `Q.GRB`, `Q.GC`, … mean the same in every machine, and
   `Ext zpBase xLogic` holds by evaluation.
   - Certificate for an all-zero row: entry `0` (not the table's beep state), side `0`,
     and gadget lengths all `0`.
   - The table file comes from `gen_table.py <name> <ident>`, which writes
     `ZP/Table<X>.lean`. It is already parametric in `lean_table`, so only the CLI
     needs wiring.

   Also emit `zpBase` (from the zp2 run) into `ZP/Logic.lean` or a new
   `ZP/LogicBase.lean`. Add every new generated file to the CI regenerate-and-diff step
   (`.github/workflows/ci.yml`, lines ~57–66).

3. **`symexec.py`:** add an optional argument naming the logic file and machine
   identifier, so segments can be designed against `zppLogic` etc. It currently
   hard-codes `ZP/Logic.lean` and `zpLogicRows%d` for `k in range(5)`, so derive the
   chunk count instead.

## Step F — Retarget the reusable N3 lemmas to `zpBase`

Mechanical but the biggest step:
1. In `Rot, Fuel, Interp, Run, Outer, Pair`, replace `zpLogic.` by `zpBase.` in every
   segment lemma and in the composites (`runFrom`, `countdown`, `fuel`, `copyLoop`,
   `gcLoop`, `qcLoop`, `wbLoop`, `decFuel`, `setup`, `sincL`, `jincL`, `dPhase`, …).
2. `lake build`. Each segment whose `decide +kernel` now fails uses a volatile
   transition. Revert exactly those to `zpLogic`. Expected: `vAcc`, `vRej*`, `vUnder`,
   the `blk*` lemmas that touch BD*, `gcEnd` (GC on M), `sinc0`/`jinc0`/`sincE`/`jincE`
   (they end in GRB via the volatile transitions), and the verifier-loop lemmas
   `vStep`, `vLoop`, `vFull`.
3. At the zp2-specific use sites in `pair_main`, lift with `zpBase_ext_zpLogic.reach`.
4. Split `ZP/Pair.lean` into `PairCore.lean` (machine-independent: copy/GC/QC/WB loops,
   `decFuel`, `setup`, `runFrom`, `dPhase`, the `bv`/`numR` arithmetic) and
   `Pair.lean` (zp2's verifier and `pair_main`).

## Step G — Generic Logical layer (`ZP/Logical.lean`)

`zpLogic_macroSim` uses only the following facts:
- `pair_step` for some `lay : Nat → Nat → ZC`;
- `zconf k0 = some (lay 1 1)` (today `k0 = 2`);
- the totality fact `ztotal`, which follows from those two.

Abstract them:

```lean
theorem lmacroSim_of_pairs (L : LTM) (C) [..] (lay : Nat → Nat → ZC) (k0 : Nat)
    (h0 : L.zconf k0 = some (lay 1 1))
    (hstep : ∀ J S, 1 ≤ J → 1 ≤ S → ∃ n, 0 < n ∧ Seg L (lay J S) n (lay (absStepC C (J,S)).1 …) (¬ C J S)) :
    Nonempty (LMacroSimC C L)
```

(`Seg` needs the machine as a parameter too.) zp2 becomes an instance.

## Step H — Generic P-side for languages over the zp2 guest (`ZP/PNP.lean`, `ZP/Decide.lean`)

These proofs never look inside `inL`. Generalize over `f : List Bool → Bool`:

```lean
def CorrectF (f) (J S : Nat) : Prop := run (str J) (str S) (clock (str J) (str S)) = f (str S)
theorem sentenceF_iff (f) : SentenceC (CorrectF f) ↔ ∃ J, ∀ s, run J s (clock J s) = f s
theorem sentenceF_of_InP (f) : InP (fun s => f s = true) → SentenceC (CorrectF f)
theorem InP_of_sentenceF (f) : SentenceC (CorrectF f) → InP (fun s => f s = true)
theorem sentenceF_iff_InP (f) : SentenceC (CorrectF f) ↔ InP (fun s => f s = true)
```

This gives `Quasihalts zXMachine ↔ InP L_X` for PP, PSPACE, FACTOR, DLOG and GI for
free, once each machine's `Quasihalts ↔ SentenceC (CorrectF inX)` is proved. Keep
`Correct`, `sentence_iff`, … as instances so `Hard.lean` is untouched.

## Done when

- `lake build` is green, and `Solution.lean` still proves
  `zp_quasihalts_iff_sentence` unchanged.
- The CI regenerate-and-diff step passes, and `gen_logic.py` with no argument
  reproduces today's `Logic.lean`.
- The following exist:
  - `zpBase`;
  - `LTM.Ext` with `.reach`;
  - `zpBase_ext_zpLogic`;
  - `macroSimC_of_logic`;
  - `lmacroSim_of_pairs`;
  - `sentenceF_iff_InP`.
- README file table updated.
