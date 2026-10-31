module

public import ZP.Defs
public import ZP.Table
public import ZP.Abstract

@[expose] public section

/-!
# Layers L0–L3: the literal table simulates the abstract program (OPEN)

This is the remaining proof obligation (formal/README.md). It is the only `sorry`
in the development, so `Solution.lean` does not pass Comparator yet.
-/

namespace ZP

theorem zp_quasihalts_iff_abstract : Quasihalts zpMachine ↔ AbstractQuasihalts := by
  sorry

end ZP
