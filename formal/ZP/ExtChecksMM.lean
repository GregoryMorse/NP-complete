module

public import ZP.Ext
public import ZP.LogicBaseMul
public import ZP.LogicMM

@[expose] public section

/-!
# `zmBase` is contained in the matrix-product machine

`zmBase` is `zp2` without the transitions that some native machine (here also `zmul`) changes.
`zmm` is `zmul` with a new output check, so every `zmBase` lemma carries over to `zmmLogic`.
-/

namespace ZP

theorem zmBase_ext_zmmLogic : zmBase.Ext zmmLogic := LTM.ext_of_extB (by decide +kernel)

end ZP
