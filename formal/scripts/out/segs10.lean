/-- K + 1 (a `0` became `1`): skip to `M_1`, erase everything right of it, write `M_a`. -/
theorem j2End (Z : List Nat) (Kr : List Nat) (X : List Nat) (b : Nat) (hZ : Sym4 Z) (hKr : Bits Kr) (hX : NoB X) (hb : b ∈ NB) :
    zppolyLogic.Reach (hdR QPoly.J2 (Z) (Kr ++ (1 :: (b :: (X))))) (hdR Q.GRB (Z ++ (Kr ++ (1 :: ([1])))) ([])) := by
  have hV : Valid [ALL, bits, NB] [Z, Kr, X] := Valid.cons hZ (Valid.cons hKr (Valid.cons hX (Valid.nil _)))
  rcases (show b = 1 ∨ b = 2 ∨ b = 3 by simpa [NB] using hb) with rfl | rfl | rfl
  · exact checkFF (env := [Z, Kr, X]) (E := []) (k := 9) hV trivial
          (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .sym 1, .blk 2 .id])
          (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Z, Kr, X]) (E := []) (k := 9) hV trivial
          (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .sym 2, .blk 2 .id])
          (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Z, Kr, X]) (E := []) (k := 9) hV trivial
          (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .sym 3, .blk 2 .id])
          (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- K + 1 (carry out): `M_1` moves right, erase the rest, write `M_a`. -/
theorem jov2End (Z : List Nat) (X : List Nat) (b : Nat) (hZ : Sym4 Z) (hX : NoB X) (hb : b ∈ NB) :
    zppolyLogic.Reach (hdR Q.JOV2 (Z) (b :: (X))) (hdR Q.GRB (Z ++ (1 :: ([1]))) ([])) := by
  have hV : Valid [ALL, NB] [Z, X] := Valid.cons hZ (Valid.cons hX (Valid.nil _))
  rcases (show b = 1 ∨ b = 2 ∨ b = 3 by simpa [NB] using hb) with rfl | rfl | rfl
  · exact checkFF (env := [Z, X]) (E := []) (k := 7) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
          (ls' := [.blk 0 .id, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Z, X]) (E := []) (k := 7) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id])
          (ls' := [.blk 0 .id, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Z, X]) (E := []) (k := 7) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id])
          (ls' := [.blk 0 .id, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- K + 1: a `0` becomes `1`. -/
theorem kinc0 (Z : List Nat) (Kr : List Nat) (X : List Nat) (b : Nat) (hZ : Sym4 Z) (hKr : Bits Kr) (hX : NoB X) (hb : b ∈ NB) :
    zppolyLogic.Reach (hdR QPoly.KINC (Z) (2 :: (Kr ++ (1 :: (b :: (X)))))) (hdR Q.GRB (Z ++ (3 :: (Kr ++ (1 :: ([1]))))) ([])) := by
  have hV : Valid [ALL, bits, NB] [Z, Kr, X] := Valid.cons hZ (Valid.cons hKr (Valid.cons hX (Valid.nil _)))
  rcases (show b = 1 ∨ b = 2 ∨ b = 3 by simpa [NB] using hb) with rfl | rfl | rfl
  · exact checkFF (env := [Z, Kr, X]) (E := []) (k := 10) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id, .sym 1, .sym 1, .blk 2 .id])
          (ls' := [.blk 0 .id, .sym 3, .blk 1 .id, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Z, Kr, X]) (E := []) (k := 10) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id])
          (ls' := [.blk 0 .id, .sym 3, .blk 1 .id, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Z, Kr, X]) (E := []) (k := 10) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id])
          (ls' := [.blk 0 .id, .sym 3, .blk 1 .id, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- K + 1: the carry leaves `K`. -/
theorem kincOv (Z : List Nat) (X : List Nat) (b : Nat) (hZ : Sym4 Z) (hX : NoB X) (hb : b ∈ NB) :
    zppolyLogic.Reach (hdR QPoly.KINC (Z) (1 :: (b :: (X)))) (hdR Q.GRB (Z ++ (2 :: (1 :: ([1])))) ([])) := by
  have hV : Valid [ALL, NB] [Z, X] := Valid.cons hZ (Valid.cons hX (Valid.nil _))
  rcases (show b = 1 ∨ b = 2 ∨ b = 3 by simpa [NB] using hb) with rfl | rfl | rfl
  · exact checkFF (env := [Z, X]) (E := []) (k := 8) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 1, .sym 1, .blk 1 .id])
          (ls' := [.blk 0 .id, .sym 2, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Z, X]) (E := []) (k := 8) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 1, .sym 2, .blk 1 .id])
          (ls' := [.blk 0 .id, .sym 2, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Z, X]) (E := []) (k := 8) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 1, .sym 3, .blk 1 .id])
          (ls' := [.blk 0 .id, .sym 2, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- K + 1: a `1` becomes `0`, carry. -/
theorem kinc1 (Z : List Nat) (R : List Nat) (hZ : Sym4 Z) (hR : Sym4 R) :
    zppolyLogic.Reach (hdR QPoly.KINC (Z) (3 :: (R))) (hdR QPoly.KINC (Z ++ ([2])) (R)) := by
  have hV : Valid [ALL, ALL] [Z, R] := Valid.cons hZ (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [Z, R]) (E := []) (k := 1) hV trivial
        (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id])
        (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
