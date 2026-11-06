import ZP.PairMainG
import ZP.GenericP
import ZP.LogicalG

/-!
# The P = GI machine quasihalts iff `SentenceG`, iff `L_GI ∈ P`
-/

namespace ZP

theorem zgiConf_two : zgiLogic.zconf 2 = some (F.layF 1 1) := rfl

/-- The pair data of `zgiLogic`: `pair_mainG` is the one lemma. -/
def zgiPairData : PairData zgiLogic CorrectG where
  lay := F.layF
  k0 := 2
  h0 := zgiConf_two
  step := G.pair_mainG

theorem zgiLogic_macroSim : Nonempty (LMacroSimC CorrectG zgiLogic) := zgiPairData.macroSim

theorem zgiQuasihalts_iff_sentence : Quasihalts zgiMachine ↔ SentenceG :=
  match zgiLogic_macroSim with
  | ⟨S⟩ => (quasihalts_iff_of_macroSimC (zgiMacroSimC S)).trans (abstractQuasihaltsC_iff (C := CorrectG))

theorem zgi_quasihalts_iff_InP :
    Quasihalts zgiMachine ↔ Cx.InP (fun s => inLG s = true) :=
  zgiQuasihalts_iff_sentence.trans (Cx.sentenceF_iff_InP inLG)

end ZP
