module

public import ZP.DefsConp

@[expose] public section

/-! Kernel-evaluated sanity checks against `ref/zconp_ref.py`. -/

namespace ZP

example : core [true, false, true, true] = [true, false] := by decide
example : core [true, true] = [] := by decide
example : core [] = [] := by decide

-- `zconp_ref.run_choice` on '110' (T = 4): the choices used are 1111 / 0111
example : runChoice (core [true, true, false]) [] 4 [] = (false, [true, true, true, true]) := by decide
example : runChoice (core [true, true, false]) [] 4 [false] = (false, [false, true, true, true]) := by decide
-- '1000' is in L, '1010' is in L, by the empty choice string
example : (runChoice (core [true, false, false, false]) [] 5 []).1 = true := by decide
example : (runChoice (core [true, false, true, false]) [] 5 []).1 = true := by decide
example : (runChoice (core [true, false, false, true]) [] 5 []).1 = false := by decide
example : inLC [true, false, false, false] := ⟨[], by decide⟩

end ZP
