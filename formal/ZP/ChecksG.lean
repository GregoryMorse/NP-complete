module

public import ZP.DefsG

@[expose] public section

/-! Kernel-evaluated sanity checks against `ref/zgi_ref.py`. -/

namespace ZP

example : inLG [] = true := by decide
-- m = 1, X = [1,1], H = [2]: in L;  m = 2, X = [1,2], H = [2,1,1,2]: not in L
example : inLG [false, true] = true := by decide
example : inLG [true, true, false, false, true, false, true, false, true] = true := by decide
example : inLG [true, true, false, true, false, true, false, true, true, false, false, true, true,
    false, true, false, true, true] = false := by decide
-- the first beeps of `zgi_ref.zp_beeps()`: ('', ''), ('0', ''), ('1', '10')
example : ¬ CorrectG 1 1 ∧ ¬ CorrectG 2 1 := by decide
set_option maxRecDepth 100000 in
example : zgiMachine.table.length = 415 := by decide

end ZP
