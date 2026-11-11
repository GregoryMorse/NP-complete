/-- Charge: a token goes to `M_t`, sweep right to the fuel. -/
theorem uvFr (Z : List Nat) (T : List Nat) (X0 : List Nat) (b : Nat) (hZ : Sym4 Z) (hT : Bits T) (hX0 : NoB X0) (hb : b ∈ bits) :
    zppolyLogic.Reach (hdR QPoly.U (Z) (b :: (T ++ (0 :: (X0))))) (hd Q.DEC1 (Z ++ (1 :: (T ++ (0 :: (X0))))) ([])) := by
  have hV : Valid [ALL, bits, NB] [Z, T, X0] := Valid.cons hZ (Valid.cons hT (Valid.cons hX0 (Valid.nil _)))
  rcases mem_bits hb with rfl | rfl
  · exact checkFT (env := [Z, T, X0]) (E := []) (k := 5) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id, .sym 0, .blk 2 .id])
          (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 0, .blk 2 .id]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [Z, T, X0]) (E := []) (k := 5) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id, .sym 0, .blk 2 .id])
          (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 0, .blk 2 .id]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Charge: first token, the gap is still `H`. -/
theorem uvFrH (Z : List Nat) (T : List Nat) (X0 : List Nat) (b : Nat) (hZ : Sym4 Z) (hT : Bits T) (hX0 : NoB X0) (hb : b ∈ bits) :
    zppolyLogic.Reach (hdR QPoly.U (Z) (b :: (T ++ (1 :: (X0))))) (hd Q.DEC1 (Z ++ (1 :: (T ++ (0 :: (X0))))) ([])) := by
  have hV : Valid [ALL, bits, NB] [Z, T, X0] := Valid.cons hZ (Valid.cons hT (Valid.cons hX0 (Valid.nil _)))
  rcases mem_bits hb with rfl | rfl
  · exact checkFT (env := [Z, T, X0]) (E := []) (k := 5) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id, .sym 1, .blk 2 .id])
          (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 0, .blk 2 .id]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [Z, T, X0]) (E := []) (k := 5) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id, .sym 1, .blk 2 .id])
          (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 0, .blk 2 .id]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Charge: back from the fuel, `M_t` moves one token right. -/
theorem fbU (Z : List Nat) (T : List Nat) (X : List Nat) (W : List Nat) (b : Nat) (hZ : Sym4 Z) (hT : Bits T) (hX : NoB X) (hW : Sym4 W) (hb : b ∈ bits) :
    zppolyLogic.Reach (hd Q.FBACK (Z ++ (1 :: (b :: (T ++ (0 :: (X)))))) (W)) (hdR QPoly.U (Z ++ ([0])) (b :: (T ++ (0 :: (X ++ (W)))))) := by
  have hV : Valid [ALL, bits, NB, ALL] [Z, T, X, W] := Valid.cons hZ (Valid.cons hT (Valid.cons hX (Valid.cons hW (Valid.nil _))))
  rcases mem_bits hb with rfl | rfl
  · exact checkTF (env := [Z, T, X, W]) (E := []) (k := 5) hV trivial
          (ls := [.blk 0 .id, .sym 1, .sym 2, .blk 1 .id, .sym 0, .blk 2 .id]) (rs := [.blk 3 .id])
          (ls' := [.blk 0 .id, .sym 0]) (rs' := [.sym 2, .blk 1 .id, .sym 0, .blk 2 .id, .blk 3 .id])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTF (env := [Z, T, X, W]) (E := []) (k := 5) hV trivial
          (ls := [.blk 0 .id, .sym 1, .sym 3, .blk 1 .id, .sym 0, .blk 2 .id]) (rs := [.blk 3 .id])
          (ls' := [.blk 0 .id, .sym 0]) (rs' := [.sym 3, .blk 1 .id, .sym 0, .blk 2 .id, .blk 3 .id])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Charge: back from the fuel, no token is left. -/
theorem fbUlast (Z : List Nat) (X : List Nat) (W : List Nat) (hZ : Sym4 Z) (hX : NoB X) (hW : Sym4 W) :
    zppolyLogic.Reach (hd Q.FBACK (Z ++ (1 :: (0 :: (X)))) (W)) (hdR QPoly.U (Z ++ ([0])) (0 :: (X ++ (W)))) := by
  have hV : Valid [ALL, NB, ALL] [Z, X, W] := Valid.cons hZ (Valid.cons hX (Valid.cons hW (Valid.nil _)))
  exact checkTF (env := [Z, X, W]) (E := []) (k := 3) hV trivial
        (ls := [.blk 0 .id, .sym 1, .sym 0, .blk 1 .id]) (rs := [.blk 2 .id])
        (ls' := [.blk 0 .id, .sym 0]) (rs' := [.sym 0, .blk 1 .id, .blk 2 .id])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Charge done: `U` meets the gap and writes `H`. -/
theorem uEnd (Z : List Nat) (X : List Nat) (hZ : Sym4 Z) (hX : NoB X) :
    zppolyLogic.Reach (hdR QPoly.U (Z) (0 :: (X))) (hdR Q.DG2 (Z ++ ([1])) (X)) := by
  have hV : Valid [ALL, NB] [Z, X] := Valid.cons hZ (Valid.cons hX (Valid.nil _))
  exact checkFF (env := [Z, X]) (E := []) (k := 1) hV trivial
        (ls := [.blk 0 .id]) (rs := [.sym 0, .blk 1 .id])
        (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
