module

public import ZP.AllDefs

@[expose] public section

/-! Kernel-evaluated sanity checks against `ref/zmh_ref.py` (`run_mh`, `in_LP`, `zp_beeps`). -/

namespace ZP

private def sb (s : String) : List Bool := s.toList.map (· == '1')

-- programs that move heads both ways and switch heads (`tests/test_native.py`)
example : runMH (sb "10100001") (sb "010") 3 = false ∧ runMH (sb "10100001") (sb "010") 5 = true := by decide
example : runMH (sb "0011010") (sb "") 1 = true := by decide
example : runMH (sb "100000") (sb "0") 40 = false ∧ runMH (sb "110000") (sb "101") 40 = false := by decide
example : runMH (sb "0010110101") (sb "11") 40 = true ∧ runMH (sb "010100") (sb "111") 40 = true := by decide
example : runMH (sb "111010000011") (sb "1110") 40 = false := by decide

-- `in_LP` on every string up to length 4 that is in `L_P`, and a sample of others
example : inLP [] = false ∧ inLP [false] = false ∧ inLP [true] = true ∧
    inLP (sb "01") = true ∧ inLP (sb "11") = true ∧ inLP (sb "10") = false ∧
    inLP (sb "1000") = true ∧ inLP (sb "1010") = true ∧ inLP (sb "1001") = false ∧
    inLP (sb "0111") = false := by decide
example : ∀ n ∈ List.range 32, 1 ≤ n → (inLP (str n) = true ↔ n ∈ [3, 5, 7, 24, 26]) := by decide

-- the first beeps of `zmh_ref.zp_beeps()`: ('', '1'), ('0', '1'), ('1', ''), ('00', '1'), ('01', '')
example : ¬ CorrectLP 1 3 ∧ ¬ CorrectLP 2 3 ∧ ¬ CorrectLP 3 1 := by decide
example : CorrectLP 1 1 ∧ CorrectLP 1 2 ∧ CorrectLP 2 1 ∧ CorrectLP 2 2 := by decide

set_option maxRecDepth 100000 in
example : zlpMachine.table.length = 373 := by decide

end ZP
