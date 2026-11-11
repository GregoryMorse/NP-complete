module

public import ZP.GenStep
public import ZP.CompilePoly
public import ZP.AbstractPoly

@[expose] public section

/-!
# Z_PPOLY: the top-level reduction to the pair lemma

`Quasihalts zppolyMachine ↔ SentencePoly` follows from `PairDataN` for `zppolyLogic` along the
abstract trajectory `polyState`, with beeps `polyOver (polyState k)`. The pair lemma (one abstract
step `polyStep` is simulated by the logical machine from `lay (polyState k)` to `lay (polyState (k+1))`,
visiting the beep state iff `polyOver`, and then once) is the remaining work of plan 12.
-/

namespace ZP

theorem zppolyQuasihalts_iff_of_pairData
    (P : PairDataN zppolyLogic (fun k => polyOver (polyState k))) :
    Quasihalts zppolyMachine ↔ SentencePoly :=
  match P.macroSim with
  | ⟨S⟩ =>
    (quasihalts_iff_of_macroSimB (Cert.macroSimB_of_logic zppolyCert zppolyCert_ok S)).trans
      abstractPoly_quasihalts_iff

end ZP
