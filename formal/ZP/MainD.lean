module

public import ZP.PairD
public import ZP.GenericP
public import ZP.LogicalG

@[expose] public section

/-!
# The DLOG machine quasihalts iff `SentenceD`, iff `L_D ∈ P`
-/

namespace ZP

theorem zdlConf_two : zdlLogic.zconf 2 = some (F.layF 1 1) := rfl

/-- The pair data of `zdlLogic`: `pair_mainD` is the one lemma. -/
def zdlPairData : PairData zdlLogic CorrectD where
  lay := F.layF
  k0 := 2
  h0 := zdlConf_two
  step := D.pair_mainD

theorem zdlLogic_macroSim : Nonempty (LMacroSimC CorrectD zdlLogic) := zdlPairData.macroSim

theorem zdlQuasihalts_iff_sentence : Quasihalts zdlMachine ↔ SentenceD :=
  match zdlLogic_macroSim with
  | ⟨S⟩ => (quasihalts_iff_of_macroSimC (zdlMacroSimC S)).trans (abstractQuasihaltsC_iff (C := CorrectD))

theorem zdl_quasihalts_iff_InP :
    Quasihalts zdlMachine ↔ Cx.InP (fun s => inLD s = true) :=
  zdlQuasihalts_iff_sentence.trans (Cx.sentenceF_iff_InP inLD)

end ZP
