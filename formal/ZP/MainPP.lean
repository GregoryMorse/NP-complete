module

public import ZP.PairPP
public import ZP.GenericP
public import ZP.LogicalG

@[expose] public section

/-!
# The P = PP machine quasihalts iff `SentencePP`, iff `L_PP ∈ P`
-/

namespace ZP

theorem zppConf_two : zppLogic.zconf 2 = some (lay 1 1) := rfl

/-- The pair data of `zppLogic`: `pair_mainPP` is the one lemma. -/
def zppPairData : PairData zppLogic CorrectPP where
  lay := lay
  k0 := 2
  h0 := zppConf_two
  step := PP.pair_mainPP

theorem zppLogic_macroSim : Nonempty (LMacroSimC CorrectPP zppLogic) := zppPairData.macroSim

theorem zppQuasihalts_iff_sentence : Quasihalts zppMachine ↔ SentencePP :=
  match zppLogic_macroSim with
  | ⟨S⟩ => (quasihalts_iff_of_macroSimC (zppMacroSimC S)).trans (abstractQuasihaltsC_iff (C := CorrectPP))

theorem zpp_quasihalts_iff_InP :
    Quasihalts zppMachine ↔ Cx.InP (fun s => inPP s = true) :=
  zppQuasihalts_iff_sentence.trans (Cx.sentenceF_iff_InP inPP)

end ZP
