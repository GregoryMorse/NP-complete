module

public import ZP.AllDefs

@[expose] public section

/-! Kernel-evaluated sanity checks against `ref/zpp_ref.py`. -/

namespace ZP

example : inPP (str 1) = false ∧ inPP (str 2) = false ∧ inPP (str 3) = true := by decide
example : inPP (str 4) = false ∧ inPP (str 5) = true ∧ inPP (str 6) = false := by decide
example : inPP (str 7) = true ∧ inPP (str 8) = false ∧ inPP (str 14) = false := by decide
-- the first beeps of `zpp_ref.zp_beeps()`: ('', '1'), ('0', '1'), ('1', '')
example : ¬ CorrectPP 1 3 ∧ ¬ CorrectPP 2 3 ∧ ¬ CorrectPP 3 1 := by decide
example : CorrectPP 1 1 ∧ CorrectPP 1 2 ∧ CorrectPP 2 1 ∧ CorrectPP 2 2 := by decide
set_option maxRecDepth 100000 in
example : zppMachine.table.length = 295 := by decide

end ZP
