/-- Charge of an empty `a`: `U` meets `H` and passes it. -/
theorem uMEnd (Z : List Nat) (X : List Nat) (hZ : Sym4 Z) (hX : NoB X) :
    zppolyLogic.Reach (hdR QPoly.U (Z) (1 :: (X))) (hdR Q.DG2 (Z ++ ([1])) (X)) := by
  have hV : Valid [ALL, NB] [Z, X] := Valid.cons hZ (Valid.cons hX (Valid.nil _))
  exact checkFF (env := [Z, X]) (E := []) (k := 1) hV trivial
        (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
        (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
