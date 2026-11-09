module

public import ZP.Ext
public import ZP.LogicBaseConp
public import ZP.LogicConp

@[expose] public section

/-!
# `zcBase` is contained in the NP = coNP machine

`zcBase` (`ZP/LogicBaseConp.lean`, `gen_logic.py baseconp`) is `zpBase` without the 10 further
transitions that `native/zconp.py` changes (`PUTH,B` `QN2,M` `BEEP,M` `DP30,M` `DP31,M` `DP40`/`DP41` on 1 and M,
`EAs,B`). Lemmas proved for `zcBase` carry over to `zconpLogic` (`LTM.Ext.reach`).
-/

namespace ZP

theorem zcBase_ext_zconpLogic : zcBase.Ext zconpLogic := LTM.ext_of_extB (by decide +kernel)

end ZP
