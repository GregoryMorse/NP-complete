module

public import ZP.PairF
public import ZP.GenericP
public import ZP.LogicalG

@[expose] public section

/-!
# The FACTOR machine quasihalts iff `SentenceF`, iff `L_F ∈ P`
-/

namespace ZP

theorem zfacConf_two : zfacLogic.zconf 2 = some (F.layF 1 1) := rfl

/-- The pair data of `zfacLogic`: `pair_mainLF` is the one lemma. -/
def zfacPairData : PairData zfacLogic CorrectF where
  lay := F.layF
  k0 := 2
  h0 := zfacConf_two
  step := F.pair_mainF

theorem zfacLogic_macroSim : Nonempty (LMacroSimC CorrectF zfacLogic) := zfacPairData.macroSim

theorem zfacQuasihalts_iff_sentence : Quasihalts zfacMachine ↔ SentenceF :=
  match zfacLogic_macroSim with
  | ⟨S⟩ => (quasihalts_iff_of_macroSimC (zfacMacroSimC S)).trans (abstractQuasihaltsC_iff (C := CorrectF))

theorem zfac_quasihalts_iff_InP :
    Quasihalts zfacMachine ↔ Cx.InP (fun s => inLF s = true) :=
  zfacQuasihalts_iff_sentence.trans (Cx.sentenceF_iff_InP inLF)

end ZP
