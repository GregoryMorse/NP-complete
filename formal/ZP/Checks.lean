module

public import ZP.Defs
public import ZP.Table

/-!
# Kernel-evaluated sanity checks

These are proved by `decide`, i.e. by evaluation in the kernel (no `native_decide`,
no extra axioms). They pin the Lean definitions to the Python reference
(`ref/zp_ref.py`) on small cases.
-/

namespace ZP

-- the empty code (J = 1) rejects everything
example : run 1 1 5 = .rej := by decide
-- accept-all: two entries (w=1, d=0, k=0), code bits "10" "10"
example : run 0b10101 3 4 = .acc := by decide
-- run-left (entry e = 4·1 + 0 + 1 = 5): loops, so the clock expires
example : run 0b1011111 1 7 = .timeout := by decide
-- the empty instance is not in L, and clocks
example : inL 1 = false := by decide
example : clock 7 5 = 16 := by decide
-- the table has the advertised size and beep state
example : zpMachine.table.length = 1371 := by decide
example : zpMachine.beep = 704 := by decide

end ZP
