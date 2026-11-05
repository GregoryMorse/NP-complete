module

public import ZP.DefsD

@[expose] public section

/-! Kernel-evaluated sanity checks against `ref/zdl_ref.py`. -/

namespace ZP

example : isPrime 0 = false ∧ isPrime 1 = false ∧ isPrime 2 = true ∧ isPrime 3 = true ∧
    isPrime 4 = false ∧ isPrime 5 = true := by decide
-- `(k, h, g, p)` = (1, 2, 2, 3), (0, 1, 2, 3), (1, 2, 2, 4), (2, 1, 1, 5), (0, 2, 3, 5)
example : inLD [true, true, false, true, true, true, false, false, true, true, true, false, false,
    true, true, true, true] = true := by decide
example : inLD [false, true, true, false, true, true, true, false, false, true, true, true, true] = true := by
  decide
example : inLD [true, true, false, true, true, true, false, false, true, true, true, false, false,
    true, true, true, false, true, false] = false := by decide
example : inLD [false, true, true, true, false, false, true, true, true, true, false, true, true,
    true, false, true, true] = false := by decide
example : inLD [] = false := by decide
-- the first beeps of `zdl_ref.zp_beeps()`: ('', '11001110'), ('0', '11001110'), ('1', '')
example : ¬ CorrectD 1 462 ∧ ¬ CorrectD 2 462 ∧ ¬ CorrectD 3 1 := by decide
set_option maxRecDepth 100000 in
example : zdlMachine.table.length = 400 := by decide

end ZP
