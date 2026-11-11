module

public import ZP.DevPolyDefs
public import ZP.AllDefs

@[expose] public section

/-! Kernel-evaluated sanity checks against `ref/zppoly_ref.py`. -/

namespace ZP

example : budget [] 0 = 1 ∧ budget [] 1 = 2 ∧ budget [false] 0 = 3 ∧ budget [false] 1 = 8 ∧
    budget [false, false] 2 = 63 := by decide
-- the first events of `zppoly_ref.events()`
-- ok('', 0, '')
example : advOK [] [] 0 := by decide
-- beep('', 1): no program of length at most 2 is good on n = 1
example : ∀ a ∈ strings 0 ++ strings 1 ++ strings 2, ¬ advOK [] a 1 := by decide
-- ok('0', 0, '')
example : advOK [false] [] 0 := by decide
-- ok('0', 1, '0001'): the programs before it are refuted
example : ∀ a ∈ strings 0 ++ strings 1 ++ strings 2 ++ strings 3, ¬ advOK [false] a 1 := by decide
example : advOK [false] [false, false, false, true] 1 := by decide
set_option maxRecDepth 100000 in
example : zppolyMachine.table.length = 325 := by decide

end ZP
