module

public import ZP.MMMain
public import ZP.CompileMM
public import ZP.GenericP
public import ZP.LogicalG

@[expose] public section

/-!
# The GF(2) matrix-product machine quasihalts iff `SentenceMM`
-/

namespace ZP

theorem zmmConf_two : zmmLogic.zconf 2 = some (Mul.layMul 1 1) := rfl

/-- The pair data of `zmmLogic`: `pair_mainMM` is the one lemma. -/
def zmmPairData : PairData zmmLogic CorrectMM where
  lay := Mul.layMul
  k0 := 2
  h0 := zmmConf_two
  step := Mul.MM.pair_mainMM

theorem zmmLogic_macroSim : Nonempty (LMacroSimC CorrectMM zmmLogic) := zmmPairData.macroSim

theorem zmmQuasihalts_iff_sentence : Quasihalts zmmMachine ↔ SentenceMM :=
  match zmmLogic_macroSim with
  | ⟨S⟩ => (quasihalts_iff_of_macroSimC (zmmMacroSimC S)).trans (abstractQuasihaltsC_iff (C := CorrectMM))

end ZP
