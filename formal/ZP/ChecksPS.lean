module

public import ZP.AllDefs

@[expose] public section

/-! Kernel-evaluated sanity checks against `ref/zps_ref.py`. -/

namespace ZP

example : inPS (str 1) = false ∧ inPS (str 2) = false ∧ inPS (str 3) = true := by decide
example : inPS (str 4) = false ∧ inPS (str 5) = true ∧ inPS (str 6) = false := by decide
example : inPS (str 7) = true ∧ inPS (str 8) = false ∧ inPS (str 12) = false := by decide
-- the first beeps of `zps_ref.zp_beeps()`: ('', '1'), ('0', '1'), ('1', '')
example : ¬ CorrectPS 1 3 ∧ ¬ CorrectPS 2 3 ∧ ¬ CorrectPS 3 1 := by decide
set_option maxRecDepth 100000 in
example : zpsMachine.table.length = 291 := by decide

end ZP
