module

public import ZP.AllDefs
public import ZP.LTM
public import ZP.Logic
public import ZP.LogicBase
public import ZP.LogicPoly
public import ZP.Ext

@[expose] public section

/-!
# `zpolyBase`: `zpBase` without the transitions that `zppoly` changes

`zppolyLogic` overrides 12 zp2 transitions (`BN3,M`, `DG3,M`, `DP10,M`, `DP11,M`, `CX,M`, `CX,1`,
`WB2,B`, `EBj,M`, and so on) and deletes the states `JE3`, `JINC`, `JOV`. `zpolyBase` is `zpBase` with exactly
those entries removed, and with the beep state `BEEPX`; the lemmas of `Rot`, `Fuel`, `Interp`, `Run` are
copied to it (`ZP/PolyRot.lean`, ...).
-/

namespace ZP

/-- The entries `(state, symbol)` of `zpBase` that differ in `zppolyLogic`. -/
def polyDel : List (Nat × Nat) :=
  [(Q.BN3, 1), (Q.CX, 1), (Q.CX, 3), (Q.DG3, 1), (Q.DP10, 1), (Q.DP11, 1), (Q.EBj, 1),
   (Q.JE3, 1), (Q.JE3, 2), (Q.JE3, 3), (Q.JINC, 1), (Q.JINC, 3), (Q.JOV, 1), (Q.JOV, 2), (Q.WB2, 0)]

def zpolyBase : LTM :=
  ⟨zpBase.table.zipIdx.map fun (row, q) =>
      row.zipIdx.map fun (c, a) => if polyDel.contains (q, a) then 0 else c, QPoly.BEEPX⟩

theorem zpolyBase_ext : zpolyBase.Ext zppolyLogic := LTM.ext_of_extB (by decide +kernel)

end ZP
