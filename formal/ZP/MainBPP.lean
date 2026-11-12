module

public import ZP.PairBPP
public import ZP.GenericP
public import ZP.LogicalG

@[expose] public section

/-!
# The promise-P = promise-BPP machine quasihalts iff `SentenceBPP`
-/

namespace ZP

theorem zbppConf_two : zbppLogic.zconf 2 = some (lay 1 1) := rfl

/-- The pair data of `zbppLogic`: `pair_mainPP` is the one lemma. -/
def zbppPairData : PairData zbppLogic CorrectBPP where
  lay := lay
  k0 := 2
  h0 := zbppConf_two
  step := BPP.pair_mainBPP

theorem zbppLogic_macroSim : Nonempty (LMacroSimC CorrectBPP zbppLogic) := zbppPairData.macroSim

theorem zbppQuasihalts_iff_sentence : Quasihalts zbppMachine ↔ SentenceBPP :=
  match zbppLogic_macroSim with
  | ⟨S⟩ => (quasihalts_iff_of_macroSimC (zbppMacroSimC S)).trans (abstractQuasihaltsC_iff (C := CorrectBPP))

end ZP
