module

public import ZP.LTM
public import ZP.Logic

@[expose] public section

/-!
# Layer N3: the logical machine runs the abstract program

`zpLogic` (`native/zp2.py`, 129 states, 4 symbols) simulates the abstract program
beep for beep and never halts. This is the one open lemma of the development; the
step from `zpLogic` to the literal 278-state table is proved in `ZP/Compile.lean`.
-/

namespace ZP

/-- OPEN: the logical machine simulates the abstract program beep for beep. -/
theorem zpLogic_macroSim : Nonempty (LMacroSim zpLogic) := by
  sorry

end ZP
