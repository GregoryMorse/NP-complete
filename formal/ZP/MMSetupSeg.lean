module

public import ZP.MMLoops
public import ZP.MMSetup
public import ZP.MMPair
public import ZP.MulCheck

@[expose] public section

/-! Setup segments (X0..X3, the copy of `s`), single steps. -/

namespace ZP.Mul.MM

open ZP
/-- X0 skips a bit. -/
theorem x0Step2 (L : List Nat) (R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd QMM.X0 (L ++ [2]) R) (hd QMM.X0 L (2 :: R)) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [L, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 2]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
/-- X1 skips a bit. -/
theorem x1Step2 (L : List Nat) (R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd QMM.X1 (L ++ [2]) R) (hd QMM.X1 L (2 :: R)) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [L, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 2]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
/-- X2 skips a bit. -/
theorem x2Step2 (L : List Nat) (R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd QMM.X2 (L ++ [2]) R) (hd QMM.X2 L (2 :: R)) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [L, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 2]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
/-- X0 skips a bit. -/
theorem x0Step3 (L : List Nat) (R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd QMM.X0 (L ++ [3]) R) (hd QMM.X0 L (3 :: R)) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [L, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
/-- X1 skips a bit. -/
theorem x1Step3 (L : List Nat) (R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd QMM.X1 (L ++ [3]) R) (hd QMM.X1 L (3 :: R)) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [L, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
/-- X2 skips a bit. -/
theorem x2Step3 (L : List Nat) (R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd QMM.X2 (L ++ [3]) R) (hd QMM.X2 L (3 :: R)) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [L, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
/-- X0 meets M_1. -/
theorem x0End (L : List Nat) (R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd QMM.X0 (L ++ [1]) R) (hd QMM.X1 L (1 :: R)) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [L, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
/-- X1 meets M_g. -/
theorem x1End (L : List Nat) (R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd QMM.X1 (L ++ [1]) R) (hd QMM.X2 L (1 :: R)) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [L, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
/-- X2 meets Ms. -/
theorem x2End (L : List Nat) (R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd QMM.X2 (L ++ [1]) R) (hd QMM.X3a L (1 :: R)) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [L, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
/-- X3a on a 1 of the ruler. -/
theorem x3a3 (L : List Nat) (R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd QMM.X3a (L ++ [3]) R) (hd QMM.X3 L (3 :: R)) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [L, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
/-- X3 skips a ruler 1. -/
theorem x3Step (L : List Nat) (R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd QMM.X3 (L ++ [3]) R) (hd QMM.X3 L (3 :: R)) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [L, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
/-- X3 on the 0: the hole H of the accumulator. -/
theorem x3Hole (L : List Nat) (R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd QMM.X3 (L ++ [2]) R) (hd QMM.SM L (0 :: R)) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [L, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 2]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 0, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
end ZP.Mul.MM
