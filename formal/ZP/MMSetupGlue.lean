module

public import ZP.MMDry2
public import ZP.MMRowsAll
public import ZP.MMBridge
public import ZP.MMVerdict3
public import ZP.MMExit
public import ZP.MMSetupLoop
public import ZP.MMRBLoop
public import ZP.MMRSLoop
public import ZP.MMFetch2

@[expose] public section

/-! Setup glue of the Z_MATMUL check: from the entry `mK1` to the first dry cycle. -/

namespace ZP.Mul.MM

open ZP

/-- The entry chain: `Rw 1 J 1 s 1 Y` becomes the copy loop's start (the separator `Ms` stays `M`). -/
theorem mkChain' (Rw : List Nat) (j : List Nat) (s : List Nat) (Y : List Nat) (hRw : Bits Rw) (hj : Bits j) (hs : Bits s) (hY : Sym4 Y) :
    zmmLogic.Reach (hdR QMM.mK1 ([1]) (Rw ++ (1 :: (j ++ (1 :: (s ++ (1 :: (Y))))))))
      (hdR Q.GC (1 :: (Rw ++ (1 :: (j ++ ([1]))))) (s ++ (0 :: (Y)))) := by
  have hV : Valid [bits, bits, bits, ALL] [Rw, j, s, Y] := Valid.cons hRw (Valid.cons hj (Valid.cons hs (Valid.cons hY (Valid.nil _))))
  exact checkFF (env := [Rw, j, s, Y]) (E := []) (k := 8) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id, .sym 0, .blk 3 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

end ZP.Mul.MM
