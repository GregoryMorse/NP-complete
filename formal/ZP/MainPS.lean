module

public import ZP.PairPS
public import ZP.GenericP
public import ZP.LogicalG

@[expose] public section

/-!
# The P = PS machine quasihalts iff `SentencePS`, iff `L_PS ∈ P`
-/

namespace ZP

theorem zpsConf_two : zpsLogic.zconf 2 = some (lay 1 1) := rfl

/-- The pair data of `zpsLogic`: `pair_mainPS` is the one lemma. -/
def zpsPairData : PairData zpsLogic CorrectPS where
  lay := lay
  k0 := 2
  h0 := zpsConf_two
  step := PS.pair_mainPS

theorem zpsLogic_macroSim : Nonempty (LMacroSimC CorrectPS zpsLogic) := zpsPairData.macroSim

theorem zpsQuasihalts_iff_sentence : Quasihalts zpsMachine ↔ SentencePS :=
  match zpsLogic_macroSim with
  | ⟨S⟩ => (quasihalts_iff_of_macroSimC (zpsMacroSimC S)).trans (abstractQuasihaltsC_iff (C := CorrectPS))

theorem zps_quasihalts_iff_InP :
    Quasihalts zpsMachine ↔ Cx.InP (fun s => inPS s = true) :=
  zpsQuasihalts_iff_sentence.trans (Cx.sentenceF_iff_InP inPS)

end ZP
