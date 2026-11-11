/-- Verifier fuel block done: write `H`, go to the guest source `C`. -/
theorem blkVer (Kr : List Nat) (a : List Nat) (s : List Nat) (C : List Nat) (hKr : Bits Kr) (ha : Bits a) (hs : Bits s) (hC : ∀ a ∈ C, a ∈ T3) :
    zppolyLogic.Reach (hdR Q.COPY (1 :: (Kr ++ (1 :: (a ++ (1 :: (s)))))) (1 :: (3 :: (C ++ (1 :: (1 :: (List.replicate s.length 3))))))) (hdR Q.GC (1 :: (1 :: (Kr ++ (1 :: (a ++ (1 :: (s ++ ([1])))))))) (3 :: (C ++ (1 :: (1 :: (List.replicate s.length 3 ++ ([3]))))))) := by
  have hV : Valid [bits, bits, bits, T3] [Kr, a, s, C] := Valid.cons hKr (Valid.cons ha (Valid.cons hs (Valid.cons hC (Valid.nil _))))
  exact checkFF (env := [Kr, a, s, C]) (E := []) (k := 27) hV trivial
        (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.sym 1, .sym 3, .blk 3 .id, .sym 1, .sym 1, .blk 2 (.const 3)])
        (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1]) (rs' := [.sym 3, .blk 3 .id, .sym 1, .sym 1, .blk 2 (.const 3), .sym 3])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
