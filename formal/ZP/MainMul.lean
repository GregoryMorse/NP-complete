module

public import ZP.MulCheck
public import ZP.CompileMul
public import ZP.GenericP
public import ZP.LogicalG

@[expose] public section

/-!
# The multiplication machine quasihalts iff `SentenceMul`
-/

namespace ZP

theorem zmulConf_two : zmulLogic.zconf 2 = some (Mul.layMul 1 1) := rfl

/-- The pair data of `zmulLogic`: `pair_mainMul` is the one lemma. -/
def zmulPairData : PairData zmulLogic CorrectMul where
  lay := Mul.layMul
  k0 := 2
  h0 := zmulConf_two
  step := Mul.pair_mainMul

theorem zmulLogic_macroSim : Nonempty (LMacroSimC CorrectMul zmulLogic) := zmulPairData.macroSim

theorem zmulQuasihalts_iff_sentence : Quasihalts zmulMachine ↔ SentenceMul :=
  match zmulLogic_macroSim with
  | ⟨S⟩ => (quasihalts_iff_of_macroSimC (zmulMacroSimC S)).trans (abstractQuasihaltsC_iff (C := CorrectMul))

end ZP
