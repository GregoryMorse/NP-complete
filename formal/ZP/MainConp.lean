module

public import ZP.ConpPair
public import ZP.CompileConp
public import ZP.GenericP
public import ZP.LogicalG

@[expose] public section

/-!
# The NP = coNP machine quasihalts iff `SentenceConp`
-/

namespace ZP

theorem zconpConf_two : zconpLogic.zconf 2 = some (Conp.layC 1 1) := rfl

/-- The pair data of `zconpLogic`: `pair_mainConp` is the one lemma. -/
def zconpPairData : PairData zconpLogic CorrectConp where
  lay := Conp.layC
  k0 := 2
  h0 := zconpConf_two
  step := Conp.pair_mainConp

theorem zconpLogic_macroSim : Nonempty (LMacroSimC CorrectConp zconpLogic) := zconpPairData.macroSim

theorem zconpQuasihalts_iff_sentence : Quasihalts zconpMachine ↔ SentenceConp :=
  match zconpLogic_macroSim with
  | ⟨S⟩ => (quasihalts_iff_of_macroSimC (zconpMacroSimC S)).trans (abstractQuasihaltsC_iff (C := CorrectConp))

end ZP
