module

public import ZP.Defs
public import ZP.Table

/-!
# Kernel-evaluated sanity checks

These are proved by `decide`, i.e. by evaluation in the kernel (no `native_decide`,
no extra axioms). They pin the Lean definitions to the Python reference
(`ref/zp2_ref.py`) on small cases.
-/

namespace ZP

-- shortlex numbering: 1 ↦ '', 2 ↦ '0', 3 ↦ '1', 6 ↦ '10'
example : str 1 = [] := by decide
example : str 3 = [true] := by decide
example : str 6 = [true, false] := by decide
-- guest runs: code '01' accepts, code '0101' rejects '' and accepts '0'
example : run [false, true] [] 6 = true := by decide
example : run [false, true, false, true] [] 6 = false := by decide
example : run [false, true, false, true] [false] 6 = true := by decide
-- membership in L: '1' and '01' are in L, '', '0', '00' are not
example : inL (str 1) = false := by decide
example : inL (str 3) = true := by decide
example : inL (str 4) = false := by decide
example : inL (str 5) = true := by decide
example : clock (str 2) (str 3) = 8 := by decide
-- the first beeps of ref/zp2_ref.zp_beeps: ('', '1'), ('0', '1'), ('1', '')
example : Correct 1 1 ∧ Correct 1 2 ∧ ¬ Correct 1 3 := by decide
example : Correct 2 1 ∧ Correct 2 2 ∧ ¬ Correct 2 3 := by decide
example : ¬ Correct 3 1 := by decide
-- the table has the advertised size and beep state
set_option maxRecDepth 100000 in
example : zpMachine.table.length = 278 := by decide
example : zpMachine.beep = 10 := by decide

end ZP
