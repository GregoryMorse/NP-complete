module

public import ZP.AllDefs

@[expose] public section

/-! Kernel-evaluated sanity checks against `ref/znl_ref.py` (`run1`, `in_LNL`, `zp_beeps`). -/

namespace ZP

private def sb (s : String) : List Bool := s.toList.map (· == '1')

-- programs that never move left agree with `run`; programs that move left differ
example : run1 (sb "1") (sb "01") 12 = run (sb "1") (sb "01") 12 := by decide
example : run1 (sb "0001011001") (sb "11") 12 = false ∧ run (sb "0001011001") (sb "11") 12 = true := by decide
example : run1 (sb "0001011101") (sb "01") 12 = false ∧ run (sb "0001011101") (sb "01") 12 = true := by decide
example : run1 (sb "0011010") [] 1 = true := by decide

-- `in_LNL` on every string up to length 4
example : ∀ n ∈ List.range 32, 1 ≤ n →
    (inLNL (str n) = true ↔ n ∈ [3, 5, 7, 17, 18, 20, 21, 25, 26]) := by decide
example : inLNL [] = false ∧ inLNL [false] = false := by decide

-- the first beeps of `znl_ref.zp_beeps()`: ('', '1'), ('0', '1'), ('1', ''), ('00', '1'), ('01', '')
example : ¬ CorrectLNL 1 3 ∧ ¬ CorrectLNL 2 3 ∧ ¬ CorrectLNL 3 1 := by decide
example : CorrectLNL 1 1 ∧ CorrectLNL 1 2 ∧ CorrectLNL 2 1 ∧ CorrectLNL 2 2 := by decide

set_option maxRecDepth 100000 in
example : zlnlMachine.table.length = 415 := by decide

end ZP
