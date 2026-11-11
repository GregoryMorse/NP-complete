/-- Wrong answer (truth flag `1`): erase the fuel, back to `s`. -/
theorem dBad0E (Kr : List Nat) (a : List Nat) (s : List Nat) (Fu : List Nat) (hKr : Bits Kr) (ha : Bits a) (hs : Bits s) (hFu : NoB Fu) :
    zppolyLogic.Reach (hdR Q.EAs (1 :: (Kr ++ (1 :: (a ++ (1 :: (s ++ (1 :: ([2])))))))) (3 :: (1 :: (Fu)))) (hd QPoly.ZS (1 :: (Kr ++ (1 :: (a ++ (1 :: (s)))))) ([])) := by
  have hV : Valid [bits, bits, bits, NB] [Kr, a, s, Fu] := Valid.cons hKr (Valid.cons ha (Valid.cons hs (Valid.cons hFu (Valid.nil _))))
  exact checkFT (env := [Kr, a, s, Fu]) (E := []) (k := 9) hV trivial
        (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 2]) (rs := [.sym 3, .sym 1, .blk 3 .id])
        (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id]) (rs' := [])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
