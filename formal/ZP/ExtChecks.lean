module

public import ZP.Ext
public import ZP.Logic
public import ZP.LogicBase
public import ZP.LogicPP
public import ZP.LogicBPP
public import ZP.LogicPS
public import ZP.LogicF
public import ZP.LogicD
public import ZP.LogicG
public import ZP.LogicBaseMul
public import ZP.LogicMul

@[expose] public section

/-!
# `zpBase` is contained in every derived machine

`zpBase` (`ZP/LogicBase.lean`) is `zp2` without the transitions that some native machine
changes, so the lemmas proved about it carry over to each of them (`LTM.Ext.reach`).
-/

namespace ZP

theorem zpBase_ext_zpLogic : zpBase.Ext zpLogic := LTM.ext_of_extB (by decide +kernel)
theorem zpBase_ext_zppLogic : zpBase.Ext zppLogic := LTM.ext_of_extB (by decide +kernel)
theorem zpBase_ext_zbppLogic : zpBase.Ext zbppLogic := LTM.ext_of_extB (by decide +kernel)
theorem zpBase_ext_zpsLogic : zpBase.Ext zpsLogic := LTM.ext_of_extB (by decide +kernel)
theorem zpBase_ext_zfacLogic : zpBase.Ext zfacLogic := LTM.ext_of_extB (by decide +kernel)
theorem zpBase_ext_zdlLogic : zpBase.Ext zdlLogic := LTM.ext_of_extB (by decide +kernel)
theorem zpBase_ext_zgiLogic : zpBase.Ext zgiLogic := LTM.ext_of_extB (by decide +kernel)

/-- `zmBase` is `zpBase` without the 16 further transitions that `zmul` changes. -/
theorem zmBase_ext_zmulLogic : zmBase.Ext zmulLogic := LTM.ext_of_extB (by decide +kernel)

end ZP
