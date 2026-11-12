/-- BLK starts: `M` at the end, back to the first bit of `s`. -/
theorem blkStart (Kl : List Nat) (Kr : List Nat) (a : List Nat) (s : List Nat) (T : List Nat) (hKl : Bits Kl) (hKr : Bits Kr) (ha : Bits a) (hs : Bits s) (hT : ∀ a ∈ T, a ∈ O13) :
    zppolyLogic.Reach (hdR Q.GRB (Kl ++ (1 :: (Kr ++ (1 :: (a ++ (1 :: (s ++ (1 :: (T))))))))) ([])) (hdR Q.COPY (Kl ++ (1 :: (Kr ++ (1 :: (a ++ ([1])))))) (s ++ (1 :: (T ++ ([1]))))) := by
  have hV : Valid [bits, bits, bits, bits, O13] [Kl, Kr, a, s, T] := Valid.cons hKl (Valid.cons hKr (Valid.cons ha (Valid.cons hs (Valid.cons hT (Valid.nil _)))))
  exact checkFF (env := [Kl, Kr, a, s, T]) (E := []) (k := 17) hV trivial
        (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id]) (rs := [])
        (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1]) (rs' := [.blk 3 .id, .sym 1, .blk 4 .id, .sym 1])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
