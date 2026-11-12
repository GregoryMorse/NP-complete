module

public import ZP.Ext
public import ZP.LogicBaseMH
public import ZP.LogicLP
public import ZP.LogicLNL

@[expose] public section

/-!
# `mhBase` is contained in the L = P and the L = NL machines

`mhBase` (`ZP/LogicBaseMH.lean`) is the intersection of `zlpLogic` and `zlnlLogic`: the part
of `zp2` that neither changes plus the multihead act, unit and erase states of `native/zmh.py`
(their numbers, namespace `QMH`, are the same in both machines). Lemmas about `mhBase`
therefore hold for the L = P machine and for the L = NL machine.
-/

namespace ZP

theorem mhBase_ext_zlpLogic : mhBase.Ext zlpLogic := LTM.ext_of_extB (by decide +kernel)
theorem mhBase_ext_zlnlLogic : mhBase.Ext zlnlLogic := LTM.ext_of_extB (by decide +kernel)

end ZP
