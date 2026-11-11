/-- Charge exhausts the fuel: `M_g` becomes `0`, the tokens are erased, `M_g` is restored, `K + 1` starts. -/
theorem exhCharge (Z : List Nat) (T : List Nat) (Y : List Nat) (W : List Nat) (hZ : Sym4 Z) (hT : Bits T) (hY : NoB Y) (hW : Sym4 W) :
    zppolyLogic.Reach (hd Q.EXH (Z ++ (1 :: (T ++ ([0])))) (1 :: (Y ++ (1 :: (W))))) (hdR QPoly.BEEPX (Z ++ (0 :: (List.replicate T.length 0 ++ (0 :: ([1]))))) (Y ++ (1 :: (W)))) := by
  have hV : Valid [ALL, bits, NB, ALL] [Z, T, Y, W] := Valid.cons hZ (Valid.cons hT (Valid.cons hY (Valid.cons hW (Valid.nil _))))
  exact checkTF (env := [Z, T, Y, W]) (E := []) (k := 8) hV trivial
        (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 0]) (rs := [.sym 1, .blk 2 .id, .sym 1, .blk 3 .id])
        (ls' := [.blk 0 .id, .sym 0, .blk 1 (.const 0), .sym 0, .sym 1]) (rs' := [.blk 2 .id, .sym 1, .blk 3 .id])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Charge exhausts the fuel with no token left. -/
theorem exhCharge0 (Z : List Nat) (Y : List Nat) (W : List Nat) (hZ : Sym4 Z) (hY : NoB Y) (hW : Sym4 W) :
    zppolyLogic.Reach (hd Q.EXH (Z ++ (1 :: ([0]))) (1 :: (Y ++ (1 :: (W))))) (hdR QPoly.BEEPX (Z ++ (0 :: (0 :: ([1])))) (Y ++ (1 :: (W)))) := by
  have hV : Valid [ALL, NB, ALL] [Z, Y, W] := Valid.cons hZ (Valid.cons hY (Valid.cons hW (Valid.nil _)))
  exact checkTF (env := [Z, Y, W]) (E := []) (k := 6) hV trivial
        (ls := [.blk 0 .id, .sym 1, .sym 0]) (rs := [.sym 1, .blk 1 .id, .sym 1, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 0, .sym 0, .sym 1]) (rs' := [.blk 1 .id, .sym 1, .blk 2 .id])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
