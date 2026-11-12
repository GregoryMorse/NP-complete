module

public import ZP.PairPolyStep

@[expose] public section

/-!
# Z_PPOLY: `Quasihalts zppolyMachine ↔ SentencePoly`

The start configuration after 5 logical steps is `layPoly (polyState 0)`; one abstract step is one
run from `layPoly` to `layPoly` of the next state (`pairStepPoly`).
-/

namespace ZP.Poly

open ZP

theorem zppoly_h0 : zppolyLogic.zconf 5 = some (layPoly (polyState 0)) := by
  rfl

def zppolyPairData : PairDataN zppolyLogic (fun k => polyOver (polyState k)) where
  lay k := layPoly (polyState k)
  k0 := 5
  h0 := zppoly_h0
  step k :=
    have hI := PInv_iter PInv_init k
    pairStepPoly (polyState k) hI.hK hI.hA hI.hv

end ZP.Poly

namespace ZP

theorem zppolyQuasihalts_iff_sentence : Quasihalts zppolyMachine ↔ SentencePoly :=
  zppolyQuasihalts_iff_of_pairData Poly.zppolyPairData

end ZP

#print axioms ZP.zppolyQuasihalts_iff_sentence
