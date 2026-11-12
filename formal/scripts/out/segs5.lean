/-- Charge: blank `M_a`, go back to the first bit of `a`. -/
theorem chargeStart (K : List Nat) (a : List Nat) (Y : List Nat) (hK : Bits K) (ha : Bits a) (hY : Sym4 Y) :
    zppolyLogic.Reach (hdR QPoly.CHS ([1]) (1 :: (K ++ (1 :: (a ++ (1 :: (Y))))))) (hdR Q.GC (1 :: (1 :: (K ++ ([1])))) (a ++ (0 :: (Y)))) := by
  have hV : Valid [bits, bits, ALL] [K, a, Y] := Valid.cons hK (Valid.cons ha (Valid.cons hY (Valid.nil _)))
  exact checkFF (env := [K, a, Y]) (E := []) (k := 7) hV trivial
        (ls := [.sym 1]) (rs := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id])
        (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id, .sym 0, .blk 2 .id])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Charge copy of `a` as tokens: one bit to the far left. -/
theorem gcBodyC (Ur : List Nat) (V : List Nat) (P : List Nat) (u : List Nat) (v : List Nat) (Rest : List Nat) (b : Nat) (hUr : Bits Ur) (hV : NoB V) (hP : Bits P) (hu : Bits u) (hv : Bits v) (hRest : Sym4 Rest) (hb : b ∈ bits) :
    zppolyLogic.Reach (hdR Q.GC (Ur ++ (1 :: (V ++ (P ++ (1 :: (u)))))) (b :: (v ++ (0 :: (Rest))))) (hdR Q.GC (b :: (Ur ++ (1 :: (V ++ (P ++ (1 :: (u ++ ([b])))))))) (v ++ (0 :: (Rest)))) := by
  have hV : Valid [bits, NB, bits, bits, bits, ALL] [Ur, V, P, u, v, Rest] := Valid.cons hUr (Valid.cons hV (Valid.cons hP (Valid.cons hu (Valid.cons hv (Valid.cons hRest (Valid.nil _))))))
  rcases mem_bits hb with rfl | rfl
  · exact checkFF (env := [Ur, V, P, u, v, Rest]) (E := []) (k := 15) hV trivial
          (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 2, .blk 4 .id, .sym 0, .blk 5 .id])
          (ls' := [.sym 2, .blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id, .sym 2]) (rs' := [.blk 4 .id, .sym 0, .blk 5 .id])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Ur, V, P, u, v, Rest]) (E := []) (k := 15) hV trivial
          (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 3, .blk 4 .id, .sym 0, .blk 5 .id])
          (ls' := [.sym 3, .blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id, .sym 3]) (rs' := [.blk 4 .id, .sym 0, .blk 5 .id])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Charge copy done: `M_a` back, to the first token. -/
theorem gcEndC (Ur : List Nat) (V : List Nat) (P : List Nat) (u : List Nat) (Rest : List Nat) (hUr : Bits Ur) (hV : NoB V) (hP : Bits P) (hu : Bits u) (hRest : Sym4 Rest) :
    zppolyLogic.Reach (hdR Q.GC (Ur ++ (1 :: (V ++ (P ++ (1 :: (u)))))) (0 :: (Rest))) (hdR QPoly.U ([]) (Ur ++ (1 :: (V ++ (P ++ (1 :: (u ++ (1 :: (Rest))))))))) := by
  have hV : Valid [bits, NB, bits, bits, ALL] [Ur, V, P, u, Rest] := Valid.cons hUr (Valid.cons hV (Valid.cons hP (Valid.cons hu (Valid.cons hRest (Valid.nil _)))))
  exact checkFF (env := [Ur, V, P, u, Rest]) (E := []) (k := 8) hV trivial
        (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 0, .blk 4 .id])
        (ls' := []) (rs' := [.blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
