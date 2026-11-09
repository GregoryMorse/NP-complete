module

public import ZP.DefsF

@[expose] public section

/-! Kernel-evaluated sanity checks against `ref/zfac_ref.py`. -/

namespace ZP

example : numbers [] = [0] ∧ numbers [true] = [0] ∧ numbers [true, true, false] = [1, 0] := by decide
example : numbers [true, false, true, true] = [1] := by decide
example : numbers [true, true, true, false, true, true, true] = [5] := by decide
example : numbers [true, true, true, false, false] = [2, 0] := by decide
example : numbers [true, true, true, false, false, true, true, true, false, true] = [2, 2] := by decide
example : numbers [true, false, false, true, true] = [0, 1] := by decide
example : inLF [true, true, true, false, false] = true := by decide
example : inLF [true, true, true, false, false, true, true, true, false, true] = true := by decide
example : inLF [true, true, true, false, true, false, false, true, true, true, false, true] = true := by decide
example : inLF [true, true, false] = false ∧ inLF [] = false ∧ inLF [true, false, false, true, true] = false := by
  decide
-- the first beeps of `zfac_ref.zp_beeps()`: ('', '11100'), ('0', '11100'), ('1', '')
example : ¬ CorrectF 1 60 ∧ ¬ CorrectF 2 60 ∧ ¬ CorrectF 3 1 := by decide
set_option maxRecDepth 100000 in
example : zfacMachine.table.length = 324 := by decide

end ZP
