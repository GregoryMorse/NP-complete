module

public import ZP.AllDefs

@[expose] public section

/-! Kernel-evaluated sanity checks against `ref/zbpp_ref.py`. -/

namespace ZP

-- `zbpp_ref.capp` on `str 1 … str 16`
example : capp (str 1) = some false ∧ capp (str 2) = some false ∧ capp (str 3) = some true ∧
    capp (str 4) = some false ∧ capp (str 5) = some true ∧ capp (str 6) = some false ∧
    capp (str 7) = some true ∧ capp (str 8) = some false := by decide
-- outside the promise: `str 17`, `str 18`, `str 20`, `str 25`, `str 26`
example : capp (str 17) = none ∧ capp (str 18) = none ∧ capp (str 19) = some false ∧
    capp (str 20) = none ∧ capp (str 21) = some true ∧ capp (str 25) = none ∧
    capp (str 26) = none := by decide
-- the first beeps of `zbpp_ref.zp_beeps()`: ('', '1'), ('0', '1'), ('1', '')
example : ¬ CorrectBPP 1 3 ∧ ¬ CorrectBPP 2 3 ∧ ¬ CorrectBPP 3 1 := by decide
example : CorrectBPP 1 1 ∧ CorrectBPP 1 2 ∧ CorrectBPP 2 1 ∧ CorrectBPP 2 2 ∧ CorrectBPP 1 17 := by decide
set_option maxRecDepth 100000 in
example : zbppMachine.table.length = 333 := by decide

end ZP
