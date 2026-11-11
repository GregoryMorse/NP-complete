module

public import ZP.MulInterp
public import ZP.LogicMM

@[expose] public section

/-! The two halting peek segments of `zmm`: `H` stays `M`, so the output check starts at `mK1` on `M`
(the cell is `1`, not the `0` that `zmul` writes). -/

namespace ZP.Mul.MM

open ZP

/-- Halting peek, `w = 1`, `d = 0`, `t = 0`: the output check starts at `mK1`; `Rw` is the output. -/
theorem segHalt1 (Qw Lw Rw W : List Nat) (g : Nat)
    (hQ : Bits Qw) (hL : Bits Lw) (hR : Bits Rw) (hW : Sym4 W) :
    zmmLogic.Reach (hd Q.FBACK (Qw ++ [2, 2, 3] ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]))
        (1 :: (Rw ++ 1 :: W)))
      (hdR QMM.mK1 [1] (Rw ++ 1 :: W)) := by
  have hv := ivalid hQ (zeros4 g) hL hR hW Sym4.nil
  exact checkTF (env := [Qw, List.replicate g 0, Lw, Rw, W, []]) (E := []) (k := 40) hv trivial
        (ls := [.blk 0 .id, .sym 2, .sym 2, .sym 3, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
        (rs := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
        (ls' := [.sym 1]) (rs' := [.blk 3 .id, .sym 1, .blk 4 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)


/-- Short entry `[true, false]`: the output check starts. -/
theorem segShort2_1 (Lw Rw W : List Nat) (g : Nat) (hL : Bits Lw) (hR : Bits Rw) (hW : Sym4 W) :
    zmmLogic.Reach (hd Q.FBACK ([2, 3] ++ List.replicate g 0 ++ 0 :: (Lw ++ [0])) (1 :: (Rw ++ 1 :: W)))
      (hdR QMM.mK1 [1] (Rw ++ 1 :: W)) := by
  have hv := ivalid Bits.nil (zeros4 g) hL hR hW Sym4.nil
  exact checkTF (env := [[], List.replicate g 0, Lw, Rw, W, []]) (E := []) (k := 64) hv trivial
    (ls := [.sym 2, .sym 3, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
    (rs := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (ls' := [.sym 1]) (rs' := [.blk 3 .id, .sym 1, .blk 4 .id])
    (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

/-! ## Write and move, then `RTW` on `Q`'s right end -/

end ZP.Mul.MM
